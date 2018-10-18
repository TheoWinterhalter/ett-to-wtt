(* This file illustrates the use of the plugin from ett to itt on examples. *)

From Translation Require Import complex_demo.

(* Definition AA := Type. *)
(* Run TemplateProgram (Θ <- TranslateConstant ε "AA" ;; tmPrint Θ). *)
(* Run TemplateProgram (TranslateConstant ε "Init.Nat.add"). *)

(* Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Θ <- tmEval Core.hnf Θ ;; tmPrint (Σi Θ)). *)

(* Definition bar := Type. *)

(* Run TemplateProgram (Translate ε "bar"). *)
(* Print barᵗ. *)

(* Definition foo (A : Type) (x : A) := x. *)

(* Run TemplateProgram (Translate ε "foo"). *)
(* Print fooᵗ. *)

(* Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}. *)

(* Run TemplateProgram (Translate ε "pseudoid"). *)
(* Print pseudoidᵗ. *)

(* Definition test (A B C : Type) (f : A -> B) (e : B = C) (u : B = A) (x : B) : C := *)
(*   {! f {! x !} !}. *)

(* Run TemplateProgram (Translate ε "test"). *)
(* Print testᵗ. *)

(* (* Definition AAmap (x :AA) := x. *) *)
(* Definition AA' := AA. *)
(* Fail Run TemplateProgram (Translate ε "AA'"). *)
(* Run TemplateProgram (Θ <- TranslateConstant ε "AA" ;; Translate Θ "AA'"). *)
(* Print AA'ᵗ. *)

(* Definition zero := 0. *)
(* Fail Run TemplateProgram (Translate ε "zero"). *)
(* Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Translate Θ "zero"). *)
(* Print zeroᵗ. *)

(* Definition nat' := nat. *)
(* Fail Run TemplateProgram (Translate ε "nat'"). *)
(* Run TemplateProgram (Θ <- TranslateConstant ε "nat" ;; Translate Θ "nat'"). *)
(* Print nat'ᵗ. *)

Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Θ <- TranslateConstant Θ "Nat.add" ;;
      Θ <- TranslateConstant Θ "vec_rect" ;;
      Translate Θ "vrev"
      (* tmPrint Θ *)
).
