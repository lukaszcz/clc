(* This file contains the basic definitions of the contraction,
   conversion and reduction relations of the systems CL-pc, CL-pc^1
   and CL-pc^L *)

Require Import general.

(*************************************************************************************)
(* basic definitions of (i-)terms and the reduction relations of CLC0 (CL-pc),
   CLC (CL-pc^1) and CLC+ (CL-pc^L) *)

Inductive iterm :=
| C : iterm
| T : iterm
| F : iterm
| I : iterm
| K : iterm
| Si : iterm
| var : nat -> iterm
| app : iterm -> iterm -> iterm.

Notation "X @i Y" := (app X Y) (at level 11, left associativity).

Inductive CtxClose_i (R : iterm -> iterm -> Prop) : iterm -> iterm -> Prop :=
| close_ibase : forall t1 t2 : iterm, R t1 t2 -> CtxClose_i R t1 t2
| close_iapp_l : forall x x' y : iterm, CtxClose_i R x x' ->
                                         CtxClose_i R (x @i y) (x' @i y)
| close_iapp_r : forall x y y' : iterm, CtxClose_i R y y' ->
                                        CtxClose_i R (x @i y) (x @i y').

Definition EqvClose_i (R : iterm -> iterm -> Prop) := clos_refl_sym_trans iterm (CtxClose_i R).

Definition RootContr_clc_base (R : iterm -> iterm -> Prop) (t1 t2 : iterm) : Prop :=
  match t1 with
  | C @i z @i x @i y =>
    (z = T /\ x = t2) \/ (z = F /\ y = t2) \/ (R x y /\ x = t2)
  | I @i x => x = t2
  | K @i x @i y => x = t2
  | Si @i x @i y @i z =>
    match t2 with
    | x1 @i z1 @i (y1 @i z2) => x = x1 /\ y = y1 /\ z = z1 /\ z = z2
    | _ => False
    end
  | _ => False
  end.

Fixpoint RootContr_clc_n (n : nat) :=
  match n with
  | 0 => RootContr_clc_base (@eq iterm)
  | S m => RootContr_clc_base (EqvClose_i (RootContr_clc_n m))
  end.

Definition Contr_clc_n n := CtxClose_i (RootContr_clc_n n).

Definition RootContr_clc0 := RootContr_clc_n 0.
Definition Contr_clc0 := CtxClose_i RootContr_clc0.
Definition Red_clc0 := clos_refl_trans iterm Contr_clc0.
Definition Eqv_clc0 := EqvClose_i RootContr_clc0.

Definition RootContr_clc x y := exists n, RootContr_clc_n n x y.
Definition Contr_clc := CtxClose_i RootContr_clc.
Definition Red_clc := clos_refl_trans iterm Contr_clc.
Definition Eqv_clc := EqvClose_i RootContr_clc.

Definition RootContr_clc_bp (R : iterm -> iterm -> Prop) (t1 t2 : iterm) : Prop :=
  RootContr_clc_base R t1 t2 \/
  match t1 with
  | C @i z @i x @i y => R x y /\ y = t2
  | _ => False
  end.

Fixpoint RootContr_clc_plus_n (n : nat) :=
  match n with
  | 0 => RootContr_clc_bp (@eq iterm)
  | S m => RootContr_clc_bp (EqvClose_i (RootContr_clc_plus_n m))
  end.

Definition RootContr_clc_plus x y := exists n, RootContr_clc_plus_n n x y.
Definition Contr_clc_plus := CtxClose_i RootContr_clc_plus.
Definition Red_clc_plus := clos_refl_trans iterm Contr_clc_plus.
Definition Eqv_clc_plus := EqvClose_i RootContr_clc_plus.
