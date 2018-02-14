
Require Import general.

Lemma lem_in_app_1 : forall {A} (a x : A) l l', In a (l ++ x :: l') -> a = x \/ In a l \/ In a l'.
Proof.
  Reconstr.hsimple Reconstr.Empty
		   (@Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		   Reconstr.Empty.
Qed.

Definition at_lem_in_app_1 {A} (a : A) := lem_in_app_1 a.

Lemma lem_in_app_2 : forall {A} (a x : A) l l', a = x \/ In a l \/ In a l' -> In a (l ++ x :: l').
Proof.
  Reconstr.htrivial Reconstr.Empty
	(@Coq.Lists.List.in_or_app, @Coq.Lists.List.in_cons)
	Reconstr.Empty.
  induction l; ycrush.
Qed.

Definition at_lem_in_app_2 {A} (a : A) := lem_in_app_2 a.

Lemma lem_skipn_length : forall {A} n (l : list A), n + length (skipn n l) >= length l.
Proof.
  induction n.
  ycrush.
  destruct l; simpl in *.
  omega.
  generalize (IHn l); omega.
Qed.

Lemma lem_firstn_len : forall {A : Type} (l : list A) l', firstn (length l) (l ++ l') = l.
Proof.
  induction l; ycrush.
Qed.

Lemma lem_skipn_len : forall {A : Type} (l : list A) l', skipn (length l) (l ++ l') = l'.
Proof.
  induction l; ycrush.
Qed.

Lemma lem_skipn_nonempty : forall {A} n (l : list A), n < length l -> is_nonempty (skipn n l).
Proof.
  intro A.
  assert (forall k n (l : list A), k + n = length l -> k > 0 -> is_nonempty (skipn n l)).
  induction k.
  ycrush.
  intros.
  pose (lem_skipn_length n l).
  assert (length (skipn n l) > 0) by omega.
  clear -H1.
  destruct (skipn n l); ycrush.
  intros; apply (H (length l - n)); omega.
Qed.

Lemma lem_firstn_preserves_elements : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
  induction n; ycrush.
Qed.

Lemma lem_skipn_preserves_elements : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
  induction n; ycrush.
Qed.

Lemma lem_map_preserves_length : forall {A} (f : A -> A) l, length (map f l) = length l.
Proof.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Lists.List.map_length)
		    Reconstr.Empty.
Qed.

Lemma lem_map_preserves_elements :
  forall {A} {B} (f : A -> B) (P : B -> Prop) l, (forall x, In x l -> P (f x)) ->
                                                 forall x, In x (map f l) -> P x.
Proof.
  Reconstr.hcrush Reconstr.Empty
	          (@Coq.Lists.List.in_map_iff)
	          Reconstr.Empty.
Qed.

Lemma lem_len_app : forall (A : Type) (l : list A) l', length l' > 0 -> length l < length (l ++ l').
Proof.
  induction l.
  ycrush.
  simpl; yintros; omega.
Qed.

Lemma lem_all_append : forall (A : Type) (P : A -> Prop) l l', (forall x, In x l -> P x) ->
                                                               (forall x, In x l' -> P x) ->
                                                               forall x, In x (l ++ l') -> P x.
Proof.
  induction l; ycrush.
Qed.

Inductive list_closure {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| lc_base : list_closure R nil nil
| lc_step : forall x x' l l', R x x' -> list_closure R l l' -> list_closure R (x :: l) (x' :: l').

Lemma lem_list_closure_refl : forall {A : Type}
                                     (R : A -> A -> Prop), (forall x, R x x) ->
                                                           forall l, list_closure R l l.
Proof.
  induction l; pose @lc_base; pose @lc_step; ycrush.
Qed.

Lemma lem_list_closure_step :
  forall {A : Type} (R : A -> A -> Prop), (forall x, R x x) ->
                                       forall x x' l l', R x x' -> list_closure R (l ++ x :: l')
                                                                                (l ++ x' :: l').
Proof.
  induction l; pose @lc_base; pose @lc_step; pose @lem_list_closure_refl; ycrush.
Qed.

Lemma lem_list_closure_trans :
  forall {A : Type} (R : A -> A -> Prop), (forall x y z, R x y -> R y z -> R x z) ->
                                       forall l2 l1 l3, list_closure R l1 l2 ->
                                                        list_closure R l2 l3 ->
                                                        list_closure R l1 l3.
Proof.
  induction l2.
  pose @lc_base; pose @lc_step; ycrush.
  intros.
  yinversion H0.
  yinversion H1.
  pose @lc_base; pose @lc_step; ycrush.
Qed.

Ltac pose_lc := pose @lc_base; pose @lc_step;
                pose @lem_list_closure_refl; pose @lem_list_closure_trans;
                pose @lem_list_closure_step.
