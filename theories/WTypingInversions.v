(* Inversion lemmata *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From Translation
Require Import util WAst WLiftSubst WTyping WEquality.
Set Keyed Unification.

Section Inversions.

Context `{Sort_notion : Sorts.notion}.

Derive NoConfusion for wterm.

Ltac destruct_pand :=
  match goal with
  | h : exists _, _ |- _ => destruct h
  | h : _ /\ _ |- _ => destruct h
  end.

Ltac destruct_pands :=
  repeat destruct_pand.

Ltac mysplit :=
  match goal with
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  end.

Ltac mysplits :=
  repeat mysplit.

Ltac invtac :=
  intros ;
  lazymatch goal with
  | h : _ |- _ =>
    dependent induction h ;
    repeat eexists ; eassumption
  end.

Lemma inversionRel :
  forall {Σ Γ n T},
    Σ ;;; Γ |-w wRel n : T ->
    exists A,
      nth_error Γ n = Some A /\
      lift0 (S n) A = T.
Proof.
  invtac.
Defined.

Lemma inversionSort :
  forall {Σ Γ s T},
    Σ ;;; Γ |-w wSort s : T ->
    wSort (Sorts.succ s) = T.
Proof.
  invtac.
Defined.

Lemma inversion_Prod :
  forall {Σ Γ A B T},
    Σ ;;; Γ |-w wProd A B : T ->
    exists s1 s2,
      Σ ;;; Γ |-w A : wSort s1 /\
      Σ ;;; Γ,, A |-w B : wSort s2 /\
      T = wSort (Sorts.prod_sort s1 s2).
Proof.
  invtac.
Defined.

Lemma inversionLambda :
  forall {Σ Γ A t T},
    Σ ;;; Γ |-w wLambda A t : T ->
      exists s1 B,
        (Σ ;;; Γ |-w A : wSort s1) /\
        (Σ ;;; Γ ,, A |-w t : B) /\
        (wProd A B = T).
Proof.
  invtac.
Defined.

Lemma inversionApp :
  forall {Σ Γ t u T},
    Σ ;;; Γ |-w wApp t u : T ->
    exists A B,
      (Σ ;;; Γ |-w t : wProd A B) /\
      (Σ ;;; Γ |-w u : A) /\
      (B{ 0 := u } = T).
Proof.
  invtac.
Defined.

Lemma inversion_Sum :
  forall {Σ Γ A B T},
    Σ ;;; Γ |-w wSum A B : T ->
    exists s1 s2,
      Σ ;;; Γ |-w A : wSort s1 /\
      Σ ;;; Γ,, A |-w B : wSort s2 /\
      T = wSort (Sorts.sum_sort s1 s2).
Proof.
  invtac.
Defined.

Lemma inversionPair :
  forall {Σ Γ A B u v T},
    Σ ;;; Γ |-w wPair A B u v : T ->
    exists s1 s2,
      (Σ ;;; Γ |-w A : wSort s1) /\
      (Σ ;;; Γ ,, A |-w B : wSort s2) /\
      (Σ ;;; Γ |-w u : A) /\
      (Σ ;;; Γ |-w v : B{ 0 := u }) /\
      (wSum A B = T).
Proof.
  invtac.
Defined.

Lemma inversionPi1 :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-w wPi1 A B p : T ->
    exists s1 s2,
      (Σ ;;; Γ |-w p : wSum A B) /\
      (Σ ;;; Γ |-w A : wSort s1) /\
      (Σ ;;; Γ ,, A |-w B : wSort s2) /\
      (A = T).
Proof.
  invtac.
Defined.

Lemma inversionPi2 :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-w wPi2 A B p : T ->
    exists s1 s2,
      (Σ ;;; Γ |-w p : wSum A B) /\
      (Σ ;;; Γ |-w A : wSort s1) /\
      (Σ ;;; Γ ,, A |-w B : wSort s2) /\
      (B{ 0 := wPi1 A B p } = T).
Proof.
  invtac.
Defined.

Lemma inversion_Eq :
  forall {Σ Γ A u v T},
    Σ ;;; Γ |-w wEq A u v : T ->
    exists s,
      Σ ;;; Γ |-w A : wSort s /\
      Σ ;;; Γ |-w u : A /\
      Σ ;;; Γ |-w v : A /\
      T = wSort (Sorts.eq_sort s).
Proof.
  invtac.
Defined.

Lemma inversionRefl :
  forall {Σ Γ A u T},
    Σ ;;; Γ |-w wRefl A u : T ->
    exists s,
      (Σ ;;; Γ |-w A : wSort s) /\
      (Σ ;;; Γ |-w u : A) /\
      (wEq A u u = T).
Proof.
  invtac.
Defined.

Lemma inversionJ :
  forall {Σ Γ A u P w v p T},
    Σ ;;; Γ |-w wJ A u P w v p : T ->
    exists s1 s2,
      (Σ ;;; Γ |-w A : wSort s1) /\
      (Σ ;;; Γ |-w u : A) /\
      (Σ ;;; Γ |-w v : A) /\
      (Σ ;;; Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0)) |-w P : wSort s2) /\
      (Σ ;;; Γ |-w p : wEq A u v) /\
      (Σ ;;; Γ |-w w : (P {1 := u}){0 := wRefl A u}) /\
      (P{1 := v}{0 := p} = T).
Proof.
  invtac.
Defined.

Lemma inversion_Transport :
  forall {Σ Γ A B p t T},
    Σ ;;; Γ |-w wTransport A B p t : T ->
    exists s,
      Σ ;;; Γ |-w A : wSort s /\
      Σ ;;; Γ |-w B : wSort s /\
      Σ ;;; Γ |-w p : wEq (wSort s) A B /\
      Σ ;;; Γ |-w t : A /\
      T = B.
Proof.
  invtac.
Defined.

Lemma inversionBeta :
  forall {Σ Γ t u T},
    Σ ;;; Γ |-w wBeta t u : T ->
    exists s A B,
      (Σ ;;; Γ,, A |-w t : B) /\
      (Σ ;;; Γ |-w u : A) /\
      (Σ ;;; Γ |-w A : wSort s) /\
      (wEq (B {0 := u}) (wApp (wLambda A t) u) (t {0 := u}) = T).
Proof.
  invtac.
Defined.

(* Lemma inversionHeq : *)
(*   forall {Σ Γ A B a b T}, *)
(*     Σ ;;; Γ |-w sHeq A a B b : T -> *)
(*     exists s, *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w B : wSort s) /\ *)
(*       (Σ ;;; Γ |-w a : A) /\ *)
(*       (Σ ;;; Γ |-w b : B) /\ *)
(*       (nl (wSort s) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionPack : *)
(*   forall {Σ Γ A1 A2 T}, *)
(*     Σ ;;; Γ |-w sPack A1 A2 : T -> *)
(*     exists s, *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (nl (wSort s) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionHeqToEq : *)
(*   forall {Σ Γ p T}, *)
(*     Σ ;;; Γ |-w sHeqToEq p : T -> *)
(*     exists A u v s, *)
(*      (Σ ;;; Γ |-w p : sHeq A u A v) /\ *)
(*      (Σ ;;; Γ |-w A : wSort s) /\ *)
(*      (Σ ;;; Γ |-w u : A) /\ *)
(*      (Σ ;;; Γ |-w v : A) /\ *)
(*      (nl (wEq A u v) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionHeqRefl : *)
(*   forall {Σ Γ A a T}, *)
(*     Σ ;;; Γ |-w sHeqRefl A a : T -> *)
(*     exists s, *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w a : A) /\ *)
(*       (nl (sHeq A a A a) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionHeqSym : *)
(*   forall {Σ Γ p T}, *)
(*     Σ ;;; Γ |-w sHeqSym p : T -> *)
(*     exists A a B b s, *)
(*       (Σ ;;; Γ |-w p : sHeq A a B b) /\ *)
(*       (Σ ;;; Γ |-w a : A) /\ *)
(*       (Σ ;;; Γ |-w b : B) /\ *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w B : wSort s) /\ *)
(*       (nl (sHeq B b A a) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionHeqTrans : *)
(*   forall {Σ Γ p q T}, *)
(*     Σ ;;; Γ |-w sHeqTrans p q : T -> *)
(*     exists A a B b C c s, *)
(*       (Σ ;;; Γ |-w p : sHeq A a B b) /\ *)
(*       (Σ ;;; Γ |-w q : sHeq B b C c) /\ *)
(*       (Σ ;;; Γ |-w a : A) /\ *)
(*       (Σ ;;; Γ |-w b : B) /\ *)
(*       (Σ ;;; Γ |-w c : C) /\ *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w B : wSort s) /\ *)
(*       (Σ ;;; Γ |-w C : wSort s) /\ *)
(*       (nl (sHeq A a C c) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionHeqTransport : *)
(*   forall {Σ Γ p t T}, *)
(*     Σ ;;; Γ |-w sHeqTransport p t : T -> *)
(*     exists A B s, *)
(*       (Σ ;;; Γ |-w p : wEq (wSort s) A B) /\ *)
(*       (Σ ;;; Γ |-w t : A) /\ *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w B : wSort s) /\ *)
(*       (nl (sHeq A t B (sTransport A B p t)) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionCongProd : *)
(*   forall {Σ Γ B1 B2 pA pB T}, *)
(*     Σ ;;; Γ |-w sCongProd B1 B2 pA pB : T -> *)
(*     exists s z nx ny A1 A2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (nl (sHeq (wSort (Sorts.prod_sort s z)) (wProd nx A1 B1) *)
(*                 (wSort (Sorts.prod_sort s z)) (wProd ny A2 B2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. Unshelve. all: constructor. *)
(* Defined. *)

(* Lemma inversionCongLambda : *)
(*   forall {Σ Γ B1 B2 t1 t2 pA pB pt T}, *)
(*     Σ ;;; Γ |-w sCongLambda B1 B2 t1 t2 pA pB pt : T -> *)
(*     exists s z nx ny A1 A2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     ((lift 1 1 t1){ 0 := sProjT1 (wRel 0) }) *)
(*                     ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) }) *)
(*                     ((lift 1 1 t2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w t1 : B1) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w t2 : B2) /\ *)
(*       (nl (sHeq (wProd nx A1 B1) (sLambda nx A1 B1 t1) *)
(*                 (wProd ny A2 B2) (sLambda ny A2 B2 t2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. Unshelve. all: constructor. *)
(* Defined. *)

(* Lemma inversionCongApp : *)
(*   forall {Σ Γ B1 B2 pu pA pB pv T}, *)
(*     Σ ;;; Γ |-w sCongApp B1 B2 pu pA pB pv : T -> *)
(*     exists s z nx ny A1 A2 u1 u2 v1 v2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w pu : sHeq (wProd nx A1 B1) u1 (wProd ny A2 B2) u2) /\ *)
(*       (Σ ;;; Γ |-w pv : sHeq A1 v1 A2 v2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (Σ ;;; Γ |-w u1 : wProd nx A1 B1) /\ *)
(*       (Σ ;;; Γ |-w u2 : wProd ny A2 B2) /\ *)
(*       (Σ ;;; Γ |-w v1 : A1) /\ *)
(*       (Σ ;;; Γ |-w v2 : A2) /\ *)
(*       (nl (sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1) *)
(*                 (B2{0 := v2}) (sApp u2 A2 B2 v2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionCongSum : *)
(*   forall {Σ Γ B1 B2 pA pB T}, *)
(*     Σ ;;; Γ |-w sCongSum B1 B2 pA pB : T -> *)
(*     exists s z nx ny A1 A2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (nl (sHeq (wSort (Sorts.sum_sort s z)) (wSum nx A1 B1) *)
(*                 (wSort (Sorts.sum_sort s z)) (wSum ny A2 B2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. Unshelve. all: constructor. *)
(* Defined. *)

(* Lemma inversionCongPair : *)
(*   forall {Σ Γ B1 B2 pA pB pu pv T}, *)
(*     Σ ;;; Γ |-w sCongPair B1 B2 pA pB pu pv : T -> *)
(*     exists s z nx ny A1 A2 u1 u2 v1 v2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w pu : sHeq A1 u1 A2 u2) /\ *)
(*       (Σ ;;; Γ |-w pv : sHeq (B1{ 0 := u1 }) v1 (B2{ 0 := u2 }) v2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (Σ ;;; Γ |-w u1 : A1) /\ *)
(*       (Σ ;;; Γ |-w u2 : A2) /\ *)
(*       (Σ ;;; Γ |-w v1 : B1{ 0 := u1 }) /\ *)
(*       (Σ ;;; Γ |-w v2 : B2{ 0 := u2 }) /\ *)
(*       (nl (sHeq (wSum nx A1 B1) (sPair A1 B1 u1 v1) *)
(*                 (wSum ny A2 B2) (sPair A2 B2 u2 v2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. Unshelve. all: constructor. *)
(* Defined. *)

(* Lemma inversionCongPi1 : *)
(*   forall {Σ Γ B1 B2 pA pB pp T}, *)
(*     Σ ;;; Γ |-w sCongPi1 B1 B2 pA pB pp : T -> *)
(*     exists s z nx ny A1 A2 p1 p2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w pp : sHeq (wSum nx A1 B1) p1 (wSum ny A2 B2) p2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (Σ ;;; Γ |-w p1 : wSum nx A1 B1) /\ *)
(*       (Σ ;;; Γ |-w p2 : wSum ny A2 B2) /\ *)
(*       (nl (sHeq A1 (sPi1 A1 B1 p1) A2 (sPi1 A2 B2 p2)) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionCongPi2 : *)
(*   forall {Σ Γ B1 B2 pA pB pp T}, *)
(*     Σ ;;; Γ |-w sCongPi2 B1 B2 pA pB pp : T -> *)
(*     exists s z nx ny A1 A2 p1 p2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ ,, (sPack A1 A2) *)
(*        |-w pB : sHeq (wSort z) ((lift 1 1 B1){ 0 := sProjT1 (wRel 0) }) *)
(*                     (wSort z) ((lift 1 1 B2){ 0 := sProjT2 (wRel 0) })) /\ *)
(*       (Σ ;;; Γ |-w pp : sHeq (wSum nx A1 B1) p1 (wSum ny A2 B2) p2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ ,, A1 |-w B1 : wSort z) /\ *)
(*       (Σ ;;; Γ ,, A2 |-w B2 : wSort z) /\ *)
(*       (Σ ;;; Γ |-w p1 : wSum nx A1 B1) /\ *)
(*       (Σ ;;; Γ |-w p2 : wSum ny A2 B2) /\ *)
(*       (nl (sHeq (B1{ 0 := sPi1 A1 B1 p1}) (sPi2 A1 B1 p1) *)
(*                 (B2{ 0 := sPi1 A2 B2 p2}) (sPi2 A2 B2 p2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionCongEq : *)
(*   forall {Σ Γ pA pu pv T}, *)
(*     Σ ;;; Γ |-w sCongEq pA pu pv : T -> *)
(*     exists s A1 A2 u1 u2 v1 v2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ |-w pu : sHeq A1 u1 A2 u2) /\ *)
(*       (Σ ;;; Γ |-w pv : sHeq A1 v1 A2 v2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w u1 : A1) /\ *)
(*       (Σ ;;; Γ |-w u2 : A2) /\ *)
(*       (Σ ;;; Γ |-w v1 : A1) /\ *)
(*       (Σ ;;; Γ |-w v2 : A2) /\ *)
(*       (nl (sHeq (wSort (Sorts.eq_sort s)) (wEq A1 u1 v1) *)
(*             (wSort (Sorts.eq_sort s)) (wEq A2 u2 v2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionCongRefl : *)
(*   forall {Σ Γ pA pu T}, *)
(*     Σ ;;; Γ |-w sCongRefl pA pu : T -> *)
(*     exists s A1 A2 u1 u2, *)
(*       (Σ ;;; Γ |-w pA : sHeq (wSort s) A1 (wSort s) A2) /\ *)
(*       (Σ ;;; Γ |-w pu : sHeq A1 u1 A2 u2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w u1 : A1) /\ *)
(*       (Σ ;;; Γ |-w u2 : A2) /\ *)
(*       (nl (sHeq (wEq A1 u1 u1) (wRefl A1 u1) *)
(*                 (wEq A2 u2 u2) (wRefl A2 u2)) *)
(*        = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionEqToHeq : *)
(*   forall {Σ Γ p T}, *)
(*     Σ ;;; Γ |-w wEqToHeq p : T -> *)
(*     exists A u v s, *)
(*       (Σ ;;; Γ |-w p : wEq A u v) /\ *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w u : A) /\ *)
(*       (Σ ;;; Γ |-w v : A) /\ *)
(*       (nl (sHeq A u A v) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionHeqTypeEq : *)
(*   forall {Σ Γ A B p T}, *)
(*     Σ ;;; Γ |-w sHeqTypeEq A B p : T -> *)
(*     exists u v s, *)
(*       (Σ ;;; Γ |-w p : sHeq A u B v) /\ *)
(*       (Σ ;;; Γ |-w A : wSort s) /\ *)
(*       (Σ ;;; Γ |-w B : wSort s) /\ *)
(*       (Σ ;;; Γ |-w u : A) /\ *)
(*       (Σ ;;; Γ |-w v : B) /\ *)
(*       (nl (wEq (wSort s) A B) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionProjT1 : *)
(*   forall {Σ Γ p T}, *)
(*     Σ ;;; Γ |-w sProjT1 p : T -> *)
(*     exists s A1 A2, *)
(*       (Σ ;;; Γ |-w p : sPack A1 A2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (nl A1 = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionProjT2 : *)
(*   forall {Σ Γ p T}, *)
(*     Σ ;;; Γ |-w sProjT2 p : T -> *)
(*     exists s A1 A2, *)
(*       (Σ ;;; Γ |-w p : sPack A1 A2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (nl A2 = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionProjTe : *)
(*   forall {Σ Γ p T}, *)
(*     Σ ;;; Γ |-w sProjTe p : T -> *)
(*     exists s A1 A2, *)
(*       (Σ ;;; Γ |-w p : sPack A1 A2) /\ *)
(*       (Σ ;;; Γ |-w A1 : wSort s) /\ *)
(*       (Σ ;;; Γ |-w A2 : wSort s) /\ *)
(*       (nl (sHeq A1 (sProjT1 p) A2 (sProjT2 p)) = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

(* Lemma inversionAx : *)
(*   forall {Σ Γ id T}, *)
(*     Σ ;;; Γ |-w wAx id : T -> *)
(*     exists ty, *)
(*       (lookup_glob Σ id = Some ty) /\ *)
(*       (nl ty = nl T). *)
(* Proof. *)
(*   invtac. *)
(* Defined. *)

End Inversions.

(* Tactic to apply inversion automatically *)

(* Ltac ttinv h := *)
(*   let s := fresh "s" in *)
(*   let s1 := fresh "s1" in *)
(*   let s2 := fresh "s2" in *)
(*   let z := fresh "z" in *)
(*   let his := fresh "is" in *)
(*   let nx := fresh "nx" in *)
(*   let ny := fresh "ny" in *)
(*   let np := fresh "np" in *)
(*   let ne := fresh "ne" in *)
(*   let na := fresh "na" in *)
(*   let A := fresh "A" in *)
(*   let B := fresh "B" in *)
(*   let C := fresh "C" in *)
(*   let A1 := fresh "A1" in *)
(*   let A2 := fresh "A2" in *)
(*   let B1 := fresh "B1" in *)
(*   let B2 := fresh "B2" in *)
(*   let u := fresh "u" in *)
(*   let v := fresh "v" in *)
(*   let u1 := fresh "u1" in *)
(*   let u2 := fresh "u2" in *)
(*   let v1 := fresh "v1" in *)
(*   let v2 := fresh "v2" in *)
(*   let p1 := fresh "p1" in *)
(*   let p2 := fresh "p2" in *)
(*   let a := fresh "a" in *)
(*   let b := fresh "b" in *)
(*   let c := fresh "c" in *)
(*   let t := fresh "t" in *)
(*   let ty := fresh "ty" in *)
(*   let univs := fresh "univs" in *)
(*   let decl := fresh "decl" in *)
(*   let isdecl := fresh "isdecl" in *)
(*   let hh := fresh "h" in *)
(*   lazymatch type of h with *)
(*   | _ ;;; _ |-w ?term : _ => *)
(*     lazymatch term with *)
(*     | wRel _ => destruct (inversionRel h) as [his hh] *)
(*     | wSort _ => pose proof (inversionSort h) as hh *)
(*     | wProd _ _ _ => destruct (inversionProd h) as (s1 & s2 & hh) ; splits_one hh *)
(*     | sLambda _ _ _ _ => destruct (inversionLambda h) as (s1 & s2 & na & hh) ; *)
(*                         splits_one hh *)
(*     | sApp _ _ _ _ => destruct (inversionApp h) as (s1 & s2 & na & hh) ; *)
(*                        splits_one hh *)
(*     | wSum _ _ _ => destruct (inversionSum h) as (s1 & s2 & hh) ; splits_one hh *)
(*     | sPair _ _ _ _ => *)
(*       destruct (inversionPair h) as (nx & s1 & s2 & hh) ; splits_one hh *)
(*     | sPi1 _ _ _ => *)
(*       destruct (inversionPi1 h) as (nx & s1 & s2 & hh) ; splits_one hh *)
(*     | sPi2 _ _ _ => *)
(*       destruct (inversionPi2 h) as (nx & s1 & s2 & hh) ; splits_one hh *)
(*     | wEq _ _ _ => destruct (inversionEq h) as (s & hh) ; splits_one hh *)
(*     | wRefl _ _ => destruct (inversionRefl h) as (s & hh) ; splits_one hh *)
(*     | wJ _ _ _ _ _ _ => destruct (inversionJ h) as (s1 & s2 & hh) ; *)
(*                        splits_one hh *)
(*     | sTransport _ _ _ _ => destruct (inversionTransport h) as (s & hh) ; *)
(*                            splits_one hh *)
(*     | sBeta _ _ => *)
(*       destruct (inversionBeta h) as (s & nx & A & B & hh) ; splits_one hh *)
(*     | sHeq _ _ _ _ => destruct (inversionHeq h) as (s & hh) ; splits_one hh *)
(*     | sHeqToEq _ => destruct (inversionHeqToEq h) as (A & u & v & s & hh) ; *)
(*                    splits_one hh *)
(*     | sHeqRefl _ _ => destruct (inversionHeqRefl h) as (s & hh) ; splits_one hh *)
(*     | sHeqSym _ => destruct (inversionHeqSym h) as (A & a & B & b & s & hh) ; *)
(*                   splits_one hh *)
(*     | sHeqTrans _ _ => *)
(*       destruct (inversionHeqTrans h) as (A & a & B & b & C & c & s & hh) ; *)
(*       splits_one hh *)
(*     | sHeqTransport _ _ => *)
(*       destruct (inversionHeqTransport h) as (A & B & s & hh) ; *)
(*       splits_one hh *)
(*     | sCongProd _ _ _ _ => *)
(*       destruct (inversionCongProd h) as (s & z & nx & ny & A1 & A2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongLambda _ _ _ _ _ _ _ => *)
(*       destruct (inversionCongLambda h) *)
(*         as (s & z & nx & ny & A1 & A2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongApp _ _ _ _ _ _ => *)
(*       destruct (inversionCongApp h) *)
(*         as (s & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongSum _ _ _ _ => *)
(*       destruct (inversionCongSum h) as (s & z & nx & ny & A1 & A2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongPair _ _ _ _ _ _ => *)
(*       destruct (inversionCongPair h) *)
(*         as (s & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongPi1 _ _ _ _ _ => *)
(*       destruct (inversionCongPi1 h) *)
(*         as (s & z & nx & ny & A1 & A2 & p1 & p2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongPi2 _ _ _ _ _ => *)
(*       destruct (inversionCongPi2 h) *)
(*         as (s & z & nx & ny & A1 & A2 & p1 & p2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongEq _ _ _ => *)
(*       destruct (inversionCongEq h) as (s & A1 & A2 & u1 & u2 & v1 & v2 & hh) ; *)
(*       splits_one hh *)
(*     | sCongRefl _ _ => *)
(*       destruct (inversionCongRefl h) as (s & A1 & A2 & u1 & u2 & hh) ; *)
(*       splits_one hh *)
(*     | wEqToHeq _ => *)
(*       destruct (inversionEqToHeq h) as (A & u & v & s & hh) ; *)
(*       splits_one hh *)
(*     | sHeqTypeEq _ _ _ => *)
(*       destruct (inversionHeqTypeEq h) as (u & v & s & hh) ; *)
(*       splits_one hh *)
(*     | sPack _ _ => destruct (inversionPack h) as (s & hh) ; splits_one hh *)
(*     | sProjT1 _ => *)
(*       destruct (inversionProjT1 h) as (s & A1 & A2 & hh) ; splits_one hh *)
(*     | sProjT2 _ => *)
(*       destruct (inversionProjT2 h) as (s & A1 & A2 & hh) ; splits_one hh *)
(*     | sProjTe _ => *)
(*       destruct (inversionProjTe h) as (s & A1 & A2 & hh) ; splits_one hh *)
(*     | sAx _ => destruct (inversionAx h) as [ty hh] ; splits_one hh *)
(*     end *)
(*   end. *)
