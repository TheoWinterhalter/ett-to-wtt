(* Quotations of terms for examples *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker.
From Translation Require Import util.

Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

Lemma vrev_eq0 : forall A m, vec A (0 + m) = vec A m.
Proof.
  reflexivity.
Defined.

Lemma vrev_eq1 : forall A n m, vec A (n + S m) = vec A (S n + m).
Proof.
  intros A n m. f_equal. omega.
Defined.