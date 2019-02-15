(*! Syntax of WTT *)
(* This one is closer to the Coq syntax, it doesn't feature annotations.
   It also removes the axioms that we want to realize and has K and funext
   instead.
   WTT is the final target of the translation.
 *)

From Template Require Import Ast.
From Translation Require Import util Sorts.

Section Ast.

Context `{Sorts.notion}.

Inductive wterm : Type :=
| wRel (n : nat)
| wSort (s : sort)
| wProd (nx : name) (A B : wterm)
| wLambda (nx : name) (A t : wterm)
| wApp (u v : wterm)
(* Σ-types *)
| wSum (nx : name) (A B : wterm)
| wPair (A B u v : wterm)
| wPi1 (A B p : wterm)
| wPi2 (A B p : wterm)
(* Homogenous equality *)
| wEq (A u v : wterm)
| wRefl (A u : wterm)
| wJ (A u P w v p : wterm)
| wTransport (A B p t : wterm)
| wBeta (t u : wterm)
| wK (A u p : wterm)
| wFunext (A B f g p : wterm)
(* Heterogenous equality *)
| wHeq (A a B b : wterm)
| wHeqPair (p q : wterm)
| wHeqTy (A B p : wterm)
| wHeqTm (p : wterm)
(* Packing *)
| wPack (A1 A2 : wterm)
| wProjT1 (p : wterm)
| wProjT2 (p : wterm)
| wProjTe (p : wterm)
(* External axioms *)
| wAx (id : ident)
.

End Ast.