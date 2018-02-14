
Require Export List.
Require Export Relations.
Require Export Classical.
Require Export ClassicalChoice.

Require Export Omega.

Require Export Reconstr.

(***********************************************************************************)
(* general definitions *)

Definition is_nonempty {A : Type} (l : list A) : Prop :=
  match l with
  | _ :: _ => True
  | _ => False
  end.

Fixpoint lst_sum (l : list nat) : nat :=
  match l with
  | h :: t => h + lst_sum t
  | nil => 0
  end.

(***********************************************************************************)
(* tactics *)

Ltac pose_rt := pose @rt_step; pose @rt_refl; pose @rt_trans.
Ltac pose_rst := pose @rst_step; pose @rst_refl; pose @rst_sym; pose @rst_trans.

Lemma lem_rst_ind :
  forall {A} (R : A -> A -> Prop) (P : A -> Prop),
    (forall x y, P x -> R x y -> P y) -> (forall x y, P x -> R y x -> P y) ->
    forall x y, clos_refl_sym_trans A R x y -> P x -> P y.
Proof.
  assert (forall {A} (R : A -> A -> Prop) (P : A -> Prop),
             (forall x y, P x -> R x y -> P y) -> (forall x y, P x -> R y x -> P y) ->
             forall x y, clos_refl_sym_trans A R x y -> (P x <-> P y)).
  intros; induction H1; ycrush.
  yauto 1.
Qed.

Ltac rst_induction z :=
  pattern z;
  lazymatch goal with
  | [ H: clos_refl_sym_trans ?A ?R1 z ?y1 |- ?G z ] =>
    apply lem_rst_ind with (R := R1) (x := y1) (y := z) (P := G);
    try solve [ pose_rst; yisolve ]; try clear H; try clear z
  | [ H: clos_refl_sym_trans ?A ?R1 ?y1 z |- ?G z ] =>
    apply lem_rst_ind with (R := R1) (x := y1) (y := z) (P := G);
    try solve [ pose_rst; yisolve ]; try clear H; try clear z
  end.

Lemma lem_rt_ind :
  forall {A} (R : A -> A -> Prop) (P : A -> Prop),
    (forall x y, P x -> R x y -> P y) ->
    forall x y, clos_refl_trans A R x y -> P x -> P y.
Proof.
  intros; induction H0; ycrush.
Qed.

Lemma lem_rt_ind_rev :
  forall {A} (R : A -> A -> Prop) (P : A -> Prop),
    (forall x y, P x -> R y x -> P y) ->
    forall x y, clos_refl_trans A R x y -> P y -> P x.
Proof.
  intros; induction H0; ycrush.
Qed.

Ltac rt_induction z :=
  pattern z;
  lazymatch goal with
  | [ H: clos_refl_trans ?A ?R1 z ?y1 |- ?G z ] =>
    apply lem_rt_ind with (R := R1) (x := z) (y := y1) (P := G);
    try solve [ pose_rt; yisolve ]; try clear H; try clear z
  | [ H: clos_refl_trans ?A ?R1 ?x1 z |- ?G z ] =>
    apply lem_rt_ind_rev with (R := R1) (x := x1) (y := z) (P := G);
    try solve [ pose_rt; yisolve ]; try clear H; try clear z
  end.
