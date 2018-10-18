(* This file illustrates the use of the plugin from ett to itt on examples. *)

From Template Require Import All.
From Translation Require Import Quotes complex_demo.
Import MonadNotation.

Definition AA := Type.
Run TemplateProgram (Θ <- TranslateConstant ε "AA" ;; tmPrint Θ).
Fail Run TemplateProgram (TranslateConstant ε "Init.Nat.add").

Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Θ <- tmEval all Θ ;; tmPrint (Σi Θ)).

Definition bar := Type.

Run TemplateProgram (Translate ε "bar").
Print barᵗ.

Definition foo (A : Type) (x : A) := x.

Run TemplateProgram (Translate ε "foo").
Print fooᵗ.

Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}.

Run TemplateProgram (Translate ε "pseudoid").
Print pseudoidᵗ.

Definition test (A B C : Type) (f : A -> B) (e : B = C) (u : B = A) (x : B) : C :=
  {! f {! x !} !}.

Run TemplateProgram (Translate ε "test").
Print testᵗ.

Definition AAmap (x :AA) := x.
Definition AA' := AA.
Fail Run TemplateProgram (Translate ε "AA'").
Run TemplateProgram (Θ <- TranslateConstant ε "AA" ;; Translate Θ "AA'").
Print AA'ᵗ.

Definition zero := 0.
Fail Run TemplateProgram (Translate ε "zero").
Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Translate Θ "zero").
Print zeroᵗ.

Definition nat' := nat.
Fail Run TemplateProgram (Translate ε "nat'").
Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Translate Θ "nat'").
Print nat'ᵗ.

Definition two := 2.
Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Translate Θ "two").
Print twoᵗ.

Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

Definition vnil' : vec nat 0 := vnil.
Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Translate Θ "vnil'"
).
Print vnil'ᵗ.

Definition vone := vcons 1 _ vnil.
Time Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      (* tmPrint Θ *)
      Translate Θ "vone"
).
Print voneᵗ.

Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

Opaque vec_rect. Opaque Init.Nat.add.
Definition vrev' :=
  Eval cbv in @vrev.
Transparent vec_rect. Transparent Init.Nat.add.

Time Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Θ <- TranslateConstant Θ "Nat.add" ;;
      Θ <- TranslateConstant Θ "vec_rect" ;;
      Translate Θ "vrev'"
).
Print vrev'ᵗ.