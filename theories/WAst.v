(*! Syntax of WTT *)
(* This one is closer to the Coq syntax, it doesn't feature annotations.
   It also removes the axioms that we want to realize and has K and funext
   instead.
   WTT is the final target of the translation.
 *)

Require Import List.
From Translation Require Import util Sorts.

Section Ast.

Context `{Sorts.notion}.

Inductive wterm : Type :=
| wRel (n : nat)
| wSort (s : sort)
| wProd (A B : wterm)
| wLambda (A t : wterm)
| wApp (u v : wterm)
(* Σ-types *)
| wSum (A B : wterm)
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
| wFunext (f g p : wterm)
| wJBeta (u P w : wterm)
| wTransportBeta (A t : wterm)
| wPairEta (p : wterm)
| wProdExt (A p : wterm)
| wSumExt (A p : wterm)
(* External axioms and defs *)
| wConst (id : ident)
| wDelta (id : ident)
.

Fixpoint mkApps u l :=
  match l with
  | nil => u
  | v :: l => mkApps (wApp u v) l
  end.

End Ast.