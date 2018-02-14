
Require Import general.
Require Import list_facts.
Require Import lterms.

Section Red.

Variable R : lterm -> lterm -> Prop.
Variable R_refl : forall x, R x x.
Variable R_trans : forall x y z, R x y -> R y z -> R x z.
Variable R_cong_ltup_0 : forall x x' y l, R x x' -> R (ltup x y l) (ltup x' y l).
Variable R_cong_ltup_1 : forall x y y' l, R y y' -> R (ltup x y l) (ltup x y' l).
Variable R_cong_ltup_2 : forall x y l1 z z' l2, R z z' -> R (ltup x y (l1 ++ z :: l2))
                                                            (ltup x y (l1 ++ z' :: l2)).

Lemma lem_red_ltup_closure_0 :
  forall l l', list_closure R l l' ->
               forall x y l0, R (ltup x y (l0 ++ l)) (ltup x y (l0 ++ l')).
Proof.
  induction l, l'; yisolve.
  intro H.
  yinversion H.
  intros.
  assert (R (ltup x y ((l1 ++ a :: nil) ++ l)) (ltup x y ((l1 ++ a :: nil) ++ l'))).
  ycrush.
  assert (HH: forall q q', (q ++ a :: nil) ++ q' = q ++ a :: q').
  induction q.
  simpl; auto with datatypes.
  simpl; intro.
  assert ((q ++ a :: nil) ++ q' = q ++ a :: q') by ycrush.
  ycrush.
  assert (R (ltup x y (l1 ++ a :: l)) (ltup x y (l1 ++ a :: l'))).
  ycrush.
  ycrush.
Qed.

Lemma lem_red_ltup_closure :
  forall x y x' y' l l', R x x' -> R y y' -> list_closure R l l' ->
                                 R (ltup x y l) (ltup x' y' l').
Proof.
  intros.
  assert (R (ltup x y (nil ++ l)) (ltup x y (nil ++ l'))).
  pose lem_red_ltup_closure_0; ycrush.
  ycrush.
Qed.

Lemma lem_red_list_closure :
  forall P l, (forall t, In t l -> exists t', R t t' /\ P t') ->
              exists l', list_closure R l l' /\ forall t, In t l' -> P t.
Proof.
  intros.
  assert (forall t, exists t', In t l -> R t t' /\ P t').
  intro t.
  assert (In t l \/ not (In t l)) by auto using classic.
  ycrush.
  assert (exists f, forall t, In t l -> R t (f t) /\ P (f t)).
  pose (choice (fun x y => In x l -> R x y /\ P y)); ycrush.
  simp_hyps.
  rename x into f.
  exists (map f l).
  clear H H0.
  induction l.
  ycrush.
  simpl in *; split; pose_lc; ycrush.
Qed.

Lemma lem_red_ltup_in :
  forall P x y l,
    (forall t, In t l -> exists t', R t t' /\ P t') ->
    exists l', R (ltup x y l) (ltup x y l') /\ forall t, In t l' -> P t.
Proof.
  pose lem_red_ltup_closure; pose lem_red_list_closure; ycrush.
Qed.

Lemma lem_red_list_closure_2 :
  forall P l, (forall t, In t l -> exists t', R t' t /\ P t') ->
              exists l', list_closure R l' l /\ forall t, In t l' -> P t.
Proof.
  intros.
  assert (forall t, exists t', In t l -> R t' t /\ P t').
  intro t.
  assert (In t l \/ not (In t l)) by auto using classic.
  ycrush.
  assert (exists f, forall t, In t l -> R (f t) t /\ P (f t)).
  pose (choice (fun x y => In x l -> R y x /\ P y)); ycrush.
  simp_hyps.
  rename x into f.
  exists (map f l).
  clear H H0.
  induction l.
  ycrush.
  simpl in *; split; pose_lc; ycrush.
Qed.

Lemma lem_red_ltup_in_2 :
  forall P x y l,
    (forall t, In t l -> exists t', R t' t /\ P t') ->
    exists l', R (ltup x y l') (ltup x y l) /\ forall t, In t l' -> P t.
Proof.
  pose lem_red_ltup_closure; pose lem_red_list_closure_2; ycrush.
Qed.

End Red.
