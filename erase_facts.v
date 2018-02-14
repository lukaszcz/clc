(* This file contains the formalisation of the basic properties of the
   relation ErasedEqv, including lemma 6 *)

Require Import general.
Require Import iterms.
Require Import lterms.

Lemma lem_erase_glue_iterms : forall x y, erase (glue_iterms x y) = erase x @i erase y.
Proof.
  destruct x, y; auto.
Qed.

Lemma rcontr_S1_erase : forall ns x y1 y2 ys z1 z2 zs t,
    RootContr_clc_s (S1 ns @l x @l (ltup y1 y2 ys) @l (ltup z1 z2 zs)) t ->
    Eqv_clc (erase t) ((erase x) @i (erase z1) @i ((erase y1) @i (erase z2))).
Proof.
  unfold RootContr_clc_s; simpl.
  yintros.
  unfold build_s_result in *.
  ydestruct ns; simpl in *.
  omega.
  assert (n > 0) by yelles 1.
  assert (exists k, n = S k).
  Reconstr.hobvious (@H6)
		    (@Coq.Arith.Gt.gt_irrefl)
		    (@Coq.Init.Nat.add, @Coq.ZArith.BinIntDef.Z.of_nat, @Coq.Lists.List.count_occ, @Coq.Arith.Compare_dec.zerop).
  simp_hyps.
  clear H6.
  subst; simpl in *.
  unfold All_pairs, ErasedEqv in *.
  ydestruct ns; cbn in *.
  ydestruct x0; cbn in *.
  ydestruct zs; cbn in *; yisolve.
  assert (Eqv_clc (erase (lterm_of_tuple (skipn x0 zs))) (erase z2)).
  ydestruct zs; cbn in *.
  omega.
  ydestruct x0; cbn in *.
  ydestruct zs; cbn in *; yelles 1.
  assert (x0 < length zs) by omega.
  assert (forall l n, n < length l -> (forall x, In x l -> In x zs) ->
                      Eqv_clc (erase (lterm_of_tuple (skipn n l))) (erase z2)).
  induction l0; cbn in *.
  intros; omega.
  yintros.
  ydestruct n; cbn in *.
  ydestruct l0; cbn in *; eauto 10.
  assert (n < length l0) by omega.
  eauto.
  ycrush.
  unfold Eqv_clc in *; eqv_solve 1.
  assert (Eqv_clc (erase (lterm_of_tuple (firstn n (skipn x0 (z2 :: zs))))) (erase z2)).
  ydestruct x0; cbn in *.
  assert (n > 0) by yelles 1.
  assert (exists k, n = S k).
  Reconstr.hobvious (@H5)
		    (@Coq.Arith.Gt.gt_irrefl)
		    (@Coq.Init.Nat.add, @Coq.ZArith.BinIntDef.Z.of_nat, @Coq.Lists.List.count_occ, @Coq.Arith.Compare_dec.zerop).
  simp_hyps.
  subst; cbn in *.
  destruct (firstn x0 zs); yelles 1.
  assert (forall l k n, k + n < length l -> n > 0 -> (forall x, In x l -> In x zs) ->
                        Eqv_clc (erase (lterm_of_tuple (firstn n (skipn k l)))) (erase z2)).
  induction l; cbn in *.
  intros; omega.
  yintros.
  ydestruct k; cbn in *.
  ydestruct n0; cbn in *.
  omega.
  ydestruct (firstn n0 l); cbn; eauto 10.
  assert (k + n0 < length l) by omega.
  eauto.
  assert (x0 + n < length zs) by omega.
  eauto.
  destruct (split_in_groups ns (skipn n (skipn x0 (z2 :: zs))));
    destruct (firstn x0 (z2 :: zs)); cbn in *; rewrite lem_erase_glue_iterms;
      unfold Eqv_clc in *; eqv_solve 1.
Qed.

Lemma rcontr_S2_erase : forall n x y z1 z2 zs t,
    RootContr_clc_s (S2 n @l x @l y @l (ltup z1 z2 zs)) t ->
    Eqv_clc (erase t) ((erase x) @i (erase z1) @i ((erase y) @i (erase z2))).
Proof.
  unfold RootContr_clc_s; cbn.
  yintros.
  assert (exists k, n = S k).
  Reconstr.hobvious (@H1)
		    (@Coq.Arith.Gt.gt_irrefl)
		    (@Coq.Init.Nat.add, @Coq.ZArith.BinIntDef.Z.of_nat, @Coq.Lists.List.count_occ, @Coq.Arith.Compare_dec.zerop).
  simp_hyps.
  clear H1.
  subst; cbn in *.
  unfold All_pairs, ErasedEqv in *.
  rewrite lem_erase_glue_iterms.
  ydestruct x0; cbn in *.
  ydestruct zs; cbn in *; yisolve.
  assert (Eqv_clc (erase (lterm_of_tuple (skipn x0 zs))) (erase z2)).
  assert (x0 < length zs) by omega.
  assert (forall l n, n < length l -> (forall x, In x l -> In x zs) ->
                      Eqv_clc (erase (lterm_of_tuple (skipn n l))) (erase z2)).
  induction l; cbn in *.
  intros; omega.
  yintros.
  ydestruct n; cbn in *.
  ydestruct l; cbn in *; eauto 10.
  assert (n < length l) by omega.
  eauto.
  ycrush.
  unfold Eqv_clc in *; eqv_solve 1.
Qed.

Lemma lem_rcontr_s_implies_erased_eqv : forall t1 t2, RootContr_clc_s t1 t2 -> ErasedEqv t1 t2.
Proof.
  intros.
  invert_rcontr_clc_s.
  unfold ErasedEqv in *.
  unfold Eqv_clc in *.
  assert (forall x y, RootContr_clc (C @i T @i erase x @i erase y) (erase x)).
  unfold RootContr_clc; cbn; exists 0; yelles 1.
  assert (forall x y, RootContr_clc (C @i F @i erase x @i erase y) (erase y)).
  unfold RootContr_clc; cbn; exists 0; yelles 1.
  destruct H0; simp_hyps; subst; cbn.
  eqv_solve 1.
  destruct H0; simp_hyps; subst; cbn.
  eqv_solve 1.
  destruct H0; simp_hyps; subst; cbn.
  pose lem_eqv_cond_l; pose lem_eqv_cond_r; pose clc_plus_to_clc0; pose eqv_clc_to_eqv_clc_plus;
    pose lem_eqv_clc0_implies_eqv_clc.
  yintuition; yelles 3.
  destruct H0; simp_hyps; subst; cbn.
  assert (RootContr_clc (I @i erase x) (erase x)).
  unfold RootContr_clc; cbn; exists 0; yelles 1.
  eqv_solve 1.
  destruct H0; simp_hyps; subst; cbn.
  assert (RootContr_clc (K @i erase x @i erase x0) (erase x)).
  unfold RootContr_clc; cbn; exists 0; yelles 1.
  eqv_solve 1.
  destruct H0; simp_hyps; subst; cbn.
  assert (exists a1 a2 al, x1 = ltup a1 a2 al).
  ydestruct x1; cbn in *; ycrush.
  assert (exists b1 b2 bl, x2 = ltup b1 b2 bl).
  ydestruct x2; cbn in *; ycrush.
  simp_hyps.
  subst; cbn in *.
  assert (Eqv_clc (erase (build_s_result x x0 (x6 :: x7 :: x8) (x3 :: x4 :: x5)))
                  (erase x0 @i erase x3 @i (erase x6 @i erase x4))).
  pose rcontr_S1_erase.
  unfold RootContr_clc_s in *; cbn in *.
  eapply e; ycrush.
  assert (Eqv_clc (erase x4) (erase x3)).
  unfold All_pairs in *; unfold Eqv_clc in *.
  eqv_solve 1.
  assert (RootContr_clc (Si @i erase x0 @i erase x6 @i erase x3) (erase x0 @i erase x3 @i (erase x6 @i erase x3))).
  unfold RootContr_clc; exists 0; cbn; ycrush.
  unfold Eqv_clc in *.
  assert (EqvClose_i RootContr_clc (Si @i erase x0 @i erase x6 @i erase x3) (erase x0 @i erase x3 @i (erase x6 @i erase x3))).
  eqv_solve 1.
  assert (EqvClose_i RootContr_clc (Si @i erase x0 @i erase x6 @i erase x3) (erase x0 @i erase x3 @i (erase x6 @i erase x4))).
  eauto using eqv_sym, eqv_cong_l, eqv_cong_r, eqv_trans.
  eqv_solve 1.
  assert (RootContr_clc (Si @i erase x0 @i erase x1 @i erase x2) (erase x0 @i erase x2 @i (erase x1 @i erase x2))).
  unfold RootContr_clc; exists 0; cbn; ycrush.
  assert (EqvClose_i RootContr_clc (Si @i erase x0 @i erase x1 @i erase x2) (erase x0 @i erase x2 @i (erase x1 @i erase x2))).
  eqv_solve 1.
  unfold All_pairs, Eqv_clc in *.
  ydestruct x2; yintuition.
  clear H0.
  assert (Eqv_clc (erase (lterm_of_tuple (firstn x (x2_1 :: x2_2 :: l)))) (erase x2_1)).
  induction x; yintuition.
  unfold Eqv_clc in *.
  ydestruct x; yintuition.
  assert (forall l0 n, n < length l0 -> (forall x, In x l0 -> In x (x2_1 :: x2_2 :: l)) ->
                      EqvClose_i RootContr_clc (erase (lterm_of_tuple (skipn n l0))) (erase x2_1)).
  induction l0; cbn in *.
  intros; omega.
  yintros.
  ydestruct n; cbn in *.
  ydestruct l0; cbn in *; eauto 10.
  assert (n < length l0) by omega.
  ycrush.
  generalize (H3 (x2_1 :: x2_2 :: l) x); intro.
  cbn in *.
  assert (EqvClose_i RootContr_clc (erase (lterm_of_tuple (skipn x (x2_1 :: x2_2 :: l)))) (erase x2_1)).
  ycrush.
  unfold Eqv_clc in *; clear -H10 H8 H0.
  assert (EqvClose_i RootContr_clc (Si @i erase x0 @i erase x1 @i erase x2_1)
    (erase x0 @i erase x2_1 @i
     (erase x1 @i erase (lterm_of_tuple (skipn x (x2_1 :: x2_2 :: l)))))).
  eqv_solve 3.
  rewrite lem_erase_glue_iterms.
  eqv_solve 4.
Qed.

(* lemma 6 *)
Lemma lem_contr_s_implies_erased_eqv : forall t1 t2, Contr_clc_s t1 t2 -> ErasedEqv t1 t2.
Proof.
  unfold Contr_clc_s.
  intros t1 t2 H.
  induction H; try solve [ unfold ErasedEqv, Eqv_clc in *; cbn; eqv_solve 1 ].
  auto using lem_rcontr_s_implies_erased_eqv.
Qed.

Lemma lem_red_s_implies_erased_eqv : forall t1 t2, Red_clc_s t1 t2 -> ErasedEqv t1 t2.
Proof.
  unfold Red_clc_s.
  intros t1 t2 H.
  induction H; try solve [ unfold ErasedEqv, Eqv_clc in *; cbn; eqv_solve 1 ].
  auto using lem_contr_s_implies_erased_eqv.
Qed.

Lemma lem_contr_s_erased_eqv : forall x y z, Contr_clc_s x y -> ErasedEqv y z -> ErasedEqv x z.
Proof.
  pose lem_contr_s_implies_erased_eqv; unfold ErasedEqv, Eqv_clc in *; eqv_eauto.
Qed.

Lemma lem_erased_eqv_sym : forall x y, ErasedEqv x y -> ErasedEqv y x.
Proof.
  unfold ErasedEqv, Eqv_clc in *; eqv_eauto.
Qed.

Lemma lem_erased_eqv_refl : forall x, ErasedEqv x x.
Proof.
  unfold ErasedEqv, Eqv_clc in *; eqv_eauto.
Qed.

Lemma lem_erased_eqv_trans : forall x y z, ErasedEqv x y -> ErasedEqv y z -> ErasedEqv x z.
Proof.
  unfold ErasedEqv, Eqv_clc in *; eqv_eauto.
Qed.

Ltac pose_erased_eqv := pose lem_contr_s_implies_erased_eqv; pose lem_contr_s_erased_eqv;
                        pose lem_erased_eqv_trans; pose lem_erased_eqv_sym; pose lem_erased_eqv_refl.
