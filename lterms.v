(* This file contains the definitions of l-terms, s-terms, the
   leftmost erasure, and proofs of their basic properties *)

Require Import general.
Require Import list_facts.
Require Import iterms.

(***********************************************************************************)
(* l-terms *)

Inductive lterm :=
| itm : iterm -> lterm
| C1 : lterm
| C2 : lterm
| T1 : lterm
| F1 : lterm
| I1 : lterm
| K1 : lterm
| S1 : list nat -> lterm
| S2 : nat -> lterm
| lapp : lterm -> lterm -> lterm
| ltup : lterm -> lterm -> list lterm -> lterm.

Notation "X @l Y" := (lapp X Y) (at level 11, left associativity).

Definition is_iterm t := match t with itm _ => true | _ => false end.

Definition lterm_ind2 :=
  fun (P : lterm -> Prop) (Q : list lterm -> Prop)
      (f : forall i : iterm, P (itm i)) (f0 : P C1) (f1 : P C2) 
      (f2 : P T1) (f3 : P F1) (fi : P I1) (f4 : P K1)
      (f5 : forall (l : list nat), P (S1 l))
      (f5' : forall (n : nat), P (S2 n))
      (f6 : forall l : lterm, P l -> forall l0 : lterm, P l0 -> P (l @l l0))
      (f7 : forall l : lterm, P l -> forall l0 : lterm, P l0 -> forall l1 : list lterm,
              Q l1 -> P (ltup l l0 l1))
      (f8 : Q nil)
      (f9 : forall x, P x -> forall l, Q l -> Q (x :: l))
=>
fix F (l : lterm) : P l :=
  match l as l0 return (P l0) with
  | itm i => f i
  | C1 => f0
  | C2 => f1
  | T1 => f2
  | F1 => f3
  | I1 => fi
  | K1 => f4
  | S1 l0 => f5 l0
  | S2 n => f5' n
  | l0 @l l1 => f6 l0 (F l0) l1 (F l1)
  | ltup l0 l1 l2 =>
    let p :=
        (fix l_ind (l : list lterm) : Q l :=
           match l with
           | nil => f8
           | h :: t => f9 h (F h) t (l_ind t)
           end) l2
    in
    f7 l0 (F l0) l1 (F l1) l2 p
  end.

Ltac lterm_induction z :=
  pattern z;
  match goal with
  | [ |- ?G z ] =>
    let t := constr:(fun l => forall z : lterm, In z l -> G z) in
    let t2 := eval simpl in t in
    induction z using lterm_ind2 with (Q := t2)
  end.

Fixpoint lsize (t : lterm) : nat :=
  match t with
  | itm _ => 0
  | C1 => 1
  | C2 => 1
  | T1 => 1
  | F1 => 1
  | I1 => 1
  | K1 => 1
  | S1 l => 1
  | S2 n => 1
  | lapp x y => lsize x + lsize y
  | ltup x y l =>
    let fix lst_lsize (l : list lterm) : nat :=
        match l with
        | nil => 0
        | h :: l' => lsize h + lst_lsize l'
        end
    in
    lsize x + lsize y + lst_lsize l
  end.

Inductive CtxClose_l (R : lterm -> lterm -> Prop) : lterm -> lterm -> Prop :=
| close_lbase : forall t1 t2 : lterm, R t1 t2 -> CtxClose_l R t1 t2
| close_lapp_l : forall x x' y : lterm, CtxClose_l R x x' ->
                                         CtxClose_l R (x @l y) (x' @l y)
| close_lapp_r : forall x y y' : lterm, CtxClose_l R y y' ->
                                         CtxClose_l R (x @l y) (x @l y')
| close_ltup_0 : forall x x' y l, CtxClose_l R x x' ->
                                  CtxClose_l R (ltup x y l) (ltup x' y l)
| close_ltup_1 : forall x y y' l, CtxClose_l R y y' ->
                                  CtxClose_l R (ltup x y l) (ltup x y' l)
| close_ltup_2 : forall x y l l' z z', CtxClose_l R z z' ->
                                       CtxClose_l R (ltup x y (l ++ (z :: l')))
                                                  (ltup x y (l ++ (z' :: l'))).

Ltac pose_ctx_l := pose close_lbase; pose close_lapp_l; pose close_lapp_r; pose close_ltup_0;
                   pose close_ltup_1; pose close_ltup_2.

Definition EqvClose_l (R : lterm -> lterm -> Prop) := clos_refl_sym_trans lterm (CtxClose_l R).

Definition tuple_of_lterm (t : lterm) : list lterm :=
  match t with
  | ltup x y l => x :: y :: l
  | _ => t :: nil
  end.

Definition lterm_of_tuple (l : list lterm) : lterm :=
  match l with
  | x :: y :: r => ltup x y r
  | x :: nil => x
  | nil => itm C (* impossible *)
  end.

Lemma lterm_tuple_cancel :
  forall t : lterm, lterm_of_tuple (tuple_of_lterm t) = t.
Proof.
  intros.
  ydestruct t; yelles 1.
Qed.

Definition is_ltup (x : lterm) : bool :=
  match x with
  | ltup _ _ _ => true
  | _ => false
  end.

Hint Unfold is_ltup : unfold_hints.

Lemma tuple_lterm_cancel_1 :
  forall l : list lterm, is_nonempty l ->
                         (forall x, In x l -> is_ltup x = false) ->
                         tuple_of_lterm (lterm_of_tuple l) = l.
Proof.
  unfold is_nonempty.
  intros.
  ydestruct l; isolve.
  simpl.
  ydestruct l0; isolve.
  ydestruct l; isolve.
  simpl.
  generalize (H0 (ltup l1 l2 l3)).
  intro.
  assert (In (ltup l1 l2 l3) (ltup l1 l2 l3 :: nil)).
  auto with datatypes.
  yauto 1.
Qed.

Lemma lem_tuple_lterm_cancel_2 :
  forall l : list lterm, length l > 1 ->
                         tuple_of_lterm (lterm_of_tuple l) = l.
Proof.
  destruct l; yisolve; destruct l0; ycrush.
Qed.

Lemma lem_tuple_len_nonzero : forall t, length (tuple_of_lterm t) > 0.
Proof.
  destruct t; yisolve.
  simpl; omega.
Qed.

Lemma lem_is_ltup_len : forall (l : list lterm), length l > 1 ->
                                                 is_ltup (lterm_of_tuple l) = true.
Proof.
  destruct l; yisolve.
  destruct l0; yisolve.
  simpl; omega.
Qed.

Inductive Sterm : lterm -> Prop :=
| sterm_c1 : Sterm C1
| sterm_c2 : Sterm C2
| sterm_t1 : Sterm T1
| sterm_f1 : Sterm F1
| sterm_i1 : Sterm I1
| sterm_k1 : Sterm K1
| sterm_s1 : forall l, Sterm (S1 l)
| sterm_s2 : forall n, Sterm (S2 n)
| sterm_lapp : forall x y, Sterm x -> Sterm (x @l y).

Ltac pose_sterm := pose sterm_c1; pose sterm_c2; pose sterm_t1; pose sterm_f1; pose sterm_k1;
                   pose sterm_s1; pose sterm_lapp.
Ltac sterm_tac n := pose_sterm; yauto n.

(* leftmost erasure *)
Fixpoint erase (t : lterm) : iterm :=
  match t with
  | itm x => x
  | C1 => C
  | C2 => C
  | T1 => T
  | F1 => F
  | I1 => I
  | K1 => K
  | S1 l => Si
  | S2 n => Si
  | lapp x y => app (erase x) (erase y)
  | ltup x y l => erase x
  end.

Definition ErasedEqv x y := Eqv_clc (erase x) (erase y).

Hint Unfold ErasedEqv : unfold_hints.

Fixpoint split_in_groups ns (l : list lterm) :=
  match ns with
  | nil => l :: nil
  | n :: ns' => firstn n l :: split_in_groups ns' (skipn n l)
  end.

Definition glue_iterms t1 t2 :=
  match t1, t2 with
  | itm x, itm y => itm (x @i y)
  | _, _ => t1 @l t2
  end.

Fixpoint build_ys ys zs :=
  match ys, zs with
  | y :: ys', tz :: zs' => (glue_iterms y (lterm_of_tuple tz)) :: build_ys ys' zs'
  | _, _ => nil
  end.

Definition build_s_result ns x l1 l2 :=
  let args := split_in_groups ns l2 in
  match args with
  | a1 :: a2 :: args' => x @l (lterm_of_tuple a1) @l lterm_of_tuple (build_ys l1 (a2 :: args'))
  | a1 :: nil => (lterm_of_tuple a1) (* impossible *)
  | _ => itm C (* impossible *)
  end.

Lemma lem_split_length :
  forall ns l, (lst_sum ns < length l) ->
               length (split_in_groups ns l) = length ns + 1.
Proof.
  induction ns; simpl.
  ycrush.
  intros.
  assert (lst_sum ns < length (skipn a l)).
  generalize (lem_skipn_length a l); omega.
  ycrush.
Qed.

Lemma lem_split_in_groups_skip :
  forall l l' ns, split_in_groups (length l :: ns) (l ++ l') = l :: split_in_groups ns l'.
Proof.
  induction l.
  ycrush.
  simpl; intros.
  rewrite lem_firstn_len.
  rewrite lem_skipn_len.
  ycrush.
Qed.

Lemma lem_split_nonempty :
  forall ns l, (forall n, In n ns -> n > 0) ->
               (lst_sum ns < length l) ->
               forall x, In x (split_in_groups ns l) -> is_nonempty x.
Proof.
  induction ns; simpl.
  ycrush.
  intros.
  ydestruct H1.
  subst.
  assert (exists k, a = S k).
  assert (a > 0) by ycrush.
  Reconstr.hobvious (@H1)
	            (@Coq.ZArith.Znat.inj_gt)
	            (@Coq.ZArith.BinIntDef.Z.of_nat, @Coq.Init.Nat.add, @Coq.ZArith.BinInt.Z.gt, @Coq.ZArith.BinIntDef.Z.compare).
  simp_hyps; subst; simpl in *.
  ydestruct l; ycrush.
  assert (lst_sum ns < length (skipn a l)).
  generalize (lem_skipn_length a l); omega.
  ycrush.
Qed.

Lemma lem_split_preserves_elements :
  forall ns l x y, In x y -> In y (split_in_groups ns l) -> In x l.
Proof.
  induction ns; simpl; yisolve.
  intros.
  ydestruct H0.
  generalize (lem_firstn_preserves_elements a l); ycrush.
  generalize (lem_skipn_preserves_elements a l); ycrush.
Qed.

Lemma lem_split_in_groups_preserves_elements_2 :
  forall x l, In x l -> forall ns, (forall n, In n ns -> n > 0) ->
                                   exists y, In x y /\ In y (split_in_groups ns l).
Proof.
  assert (forall x l, In x l ->
                      forall n ns, (forall n, In n ns -> n > 0) ->
                                   In x (firstn n l) \/
                                   exists y, In x y /\
                                             In y (split_in_groups ns (skipn n l))).
  induction l.
  ycrush.
  simpl.
  induction n.
  simpl.
  destruct ns.
  Reconstr.hsimple (@H)
	           (@Coq.Lists.List.not_in_cons, @Coq.Lists.List.in_cons)
		   Reconstr.Empty.
  simpl.
  ydestruct n.
  firstorder with arith.
  simpl.
  intros.
  destruct H.
  subst.
  right; exists (x :: firstn n l).
  simpl; firstorder with datatypes.
  assert (HH: In x (firstn n l) \/
              (exists y : list lterm, In x y /\ In y (split_in_groups ns (skipn n l)))).
  ycrush.
  destruct HH.
  assert (In x (a :: firstn n l)) by ycrush.
  ycrush.
  ycrush.
  simpl; firstorder.
  intros; yforwarding.
  generalize (H2 0); simpl; intro.
  firstorder.
Qed.

Lemma lem_split_result :
  forall n ns l, exists a b s, split_in_groups (n :: ns) l = a :: b :: s.
Proof.
  destruct ns; ycrush.
Qed.

Definition All_pairs {A : Type} (l : list A) (R : A -> A -> Prop) :=
  forall x y, In x l -> In y l -> R x y.

Hint Unfold All_pairs : yhints.

Definition RootContr_S (t1 t2 : lterm) : Prop :=
  match t1 with
  | S1 ns @l x @l ys @l zs =>
    (forall n, In n ns -> n > 0) /\
    is_ltup ys = true /\ is_ltup zs = true /\
    let l1 := tuple_of_lterm ys in
    let l2 := tuple_of_lterm zs in
    (forall x, In x l2 -> is_ltup x = false) /\
    length l1 = length ns /\
    lst_sum ns < length l2 /\
    All_pairs l1 ErasedEqv /\
    All_pairs l2 ErasedEqv /\
    t2 = build_s_result ns x l1 l2
  | S2 n @l x @l y @l zs =>
    is_ltup y = false /\ is_ltup zs = true /\
    let l := tuple_of_lterm zs in
    (forall x, In x l -> is_ltup x = false) /\
    n > 0 /\ n < length l /\
    All_pairs l ErasedEqv /\
    t2 = x @l (lterm_of_tuple (firstn n l)) @l glue_iterms y (lterm_of_tuple (skipn n l))
  | _ => False
  end.

Definition RootContr_clc_s_minus (t1 t2 : lterm) : Prop :=
  match t1 with
  | C1 @l T1 @l x @l y => t2 = x
  | C1 @l F1 @l x @l y => t2 = y
  | C2 @l z @l x @l y => t2 = x /\ ErasedEqv x y
  | I1 @l x => t2 = x
  | K1 @l x @l y => t2 = x
  | _ => RootContr_S t1 t2
  end.

Definition RootContr_clc_s (t1 t2 : lterm) : Prop :=
  match t1 with
  | C1 @l T1 @l x @l y => t2 = x
  | C1 @l F1 @l x @l y => t2 = y
  | C2 @l z @l x @l y => (t2 = x \/ t2 = y) /\ ErasedEqv x y
  | I1 @l x => t2 = x
  | K1 @l x @l y => t2 = x
  | _ => RootContr_S t1 t2
  end.

Definition Contr_clc_s := CtxClose_l RootContr_clc_s.
Definition Red_clc_s := clos_refl_trans lterm Contr_clc_s.

Inductive Contr_clc_s_minus : lterm -> lterm -> Prop :=
| s_minus_base : forall t1 t2 : lterm, RootContr_clc_s_minus t1 t2 -> Contr_clc_s_minus t1 t2
| s_minus_lapp_l : forall x x' y : lterm, Contr_clc_s_minus x x' ->
                                          Contr_clc_s_minus (x @l y) (x' @l y)
| s_minus_lapp_r : forall x y y' : lterm, Contr_clc_s_minus y y' ->
                                          Contr_clc_s_minus (x @l y) (x @l y').
Definition Red_clc_s_minus := clos_refl_trans lterm Contr_clc_s_minus.

Ltac pose_s_minus := pose s_minus_base; pose s_minus_lapp_l; pose s_minus_lapp_r.

Definition Redex_clc_s t :=
  match t with
  | C1 @l T1 @l x @l y => True
  | C1 @l F1 @l x @l y => True
  | C2 @l z @l x @l y => ErasedEqv x y
  | I1 @l x => True
  | K1 @l x @l y => True
  | S1 ns @l x @l ys @l zs =>
    (forall n, In n ns -> n > 0) /\
    is_ltup ys = true /\ is_ltup zs = true /\
    let l1 := tuple_of_lterm ys in
    let l2 := tuple_of_lterm zs in
    (forall x, In x l2 -> is_ltup x = false) /\
    length l1 = length ns /\
    lst_sum ns < length l2 /\
    All_pairs l1 ErasedEqv /\
    All_pairs l2 ErasedEqv
  | S2 n @l x @l y @l zs =>
    is_ltup y = false /\ is_ltup zs = true /\
    let l := tuple_of_lterm zs in
    (forall x, In x l -> is_ltup x = false) /\
    n > 0 /\ n < length l /\
    All_pairs l ErasedEqv
  | _ => False
  end.

Lemma rcontr_S_inversion :
  forall t1 t2, RootContr_S t1 t2 ->
                (exists ns x ys zs, t1 = S1 ns @l x @l ys @l zs /\
                                      (forall n, In n ns -> n > 0) /\
                                      is_ltup ys = true /\ is_ltup zs = true /\
                                      let l1 := tuple_of_lterm ys in
                                      let l2 := tuple_of_lterm zs in
                                      (forall x, In x l2 -> is_ltup x = false) /\
                                      length l1 = length ns /\
                                      lst_sum ns < length l2 /\
                                      All_pairs l1 ErasedEqv /\
                                      All_pairs l2 ErasedEqv /\
                                      t2 = build_s_result ns x l1 l2) \/
                (exists n x y zs, t1 = S2 n @l x @l y @l zs /\
                                  is_ltup y = false /\ is_ltup zs = true /\
                                  let l := tuple_of_lterm zs in
                                  (forall x, In x l -> is_ltup x = false) /\
                                  n > 0 /\ n < length l /\
                                  All_pairs l ErasedEqv /\
                                  t2 = (x @l (lterm_of_tuple (firstn n l)) @l
                                          glue_iterms y (lterm_of_tuple (skipn n l)))).
Proof.
  intros; ydestruct t1; simpl in *; yisolve.
Qed.

Ltac invert_rcontr_S :=
  repeat match goal with
         | [ H : (RootContr_S ?x ?y) |- _ ] =>
           generalize (rcontr_S_inversion x y H); yintro; clear H
         end.

Lemma rcontr_clc_s_inversion :
  forall t1 t2, RootContr_clc_s t1 t2 ->
                (exists x y, t1 = C1 @l T1 @l x @l y /\ t2 = x) \/
                (exists x y, t1 = C1 @l F1 @l x @l y /\ t2 = y) \/
                (exists x y z, t1 = C2 @l z @l x @l y /\ (t2 = x \/ t2 = y) /\ ErasedEqv x y) \/
                (exists x, t1 = I1 @l x /\ t2 = x) \/
                (exists x y, t1 = K1 @l x @l y /\ t2 = x) \/
                (exists ns x ys zs, t1 = S1 ns @l x @l ys @l zs /\
                                      (forall n, In n ns -> n > 0) /\
                                      is_ltup ys = true /\ is_ltup zs = true /\
                                      let l1 := tuple_of_lterm ys in
                                      let l2 := tuple_of_lterm zs in
                                      (forall x, In x l2 -> is_ltup x = false) /\
                                      length l1 = length ns /\
                                      lst_sum ns < length l2 /\
                                      All_pairs l1 ErasedEqv /\
                                      All_pairs l2 ErasedEqv /\
                                      t2 = build_s_result ns x l1 l2) \/
                (exists n x y zs, t1 = S2 n @l x @l y @l zs /\
                                  is_ltup y = false /\ is_ltup zs = true /\
                                  let l := tuple_of_lterm zs in
                                  (forall x, In x l -> is_ltup x = false) /\
                                  n > 0 /\ n < length l /\
                                  All_pairs l ErasedEqv /\
                                  t2 = (x @l (lterm_of_tuple (firstn n l)) @l
                                          glue_iterms y (lterm_of_tuple (skipn n l)))).
Proof.
  intros; ydestruct t1; simpl in *; yisolve.
Qed.

Ltac invert_rcontr_clc_s :=
  repeat match goal with
         | [ H : (RootContr_clc_s ?x ?y) |- ?G ] =>
           generalize (rcontr_clc_s_inversion x y H); yintro; clear H
         end.

Lemma invert_rcontr_c :
  forall z x y t, RootContr_clc_s (C1 @l z @l x @l y) t \/ RootContr_clc_s (C2 @l z @l x @l y) t ->
                  t = x \/ t = y.
Proof.
  intros; intuition; invert_rcontr_clc_s; yisolve.
Qed.

Lemma lem_rcontr_clc_s_implies_redex : forall x y, RootContr_clc_s x y -> Redex_clc_s x.
Proof.
  intros; invert_rcontr_clc_s; ydestruct x; ycrush.
Qed.

Lemma lem_redex_clc_s_implies_rcontr : forall x, Redex_clc_s x -> exists y, RootContr_clc_s x y.
Proof.
  intros; ydestruct x; simpl in *; yisolve.
Qed.

Lemma lem_sterm_glue_iterms : forall x y, Sterm (x @l y) -> glue_iterms x y = x @l y.
Proof.
  ycrush.
Qed.

Lemma lem_s2_discriminate_y : forall n x y z, y <> S2 n @l x @l y @l z.
Proof.
  autounfold; intros.
  assert (lsize y = lsize (S2 n @l x @l y @l z)) by ycrush.
  simpl in *; omega.
Qed.
