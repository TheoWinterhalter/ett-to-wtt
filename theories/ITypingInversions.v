(* Inversion lemmata *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon ITyping.

Section Inversions.

Context `{Sort_notion : Sorts.notion}.

Open Scope i_scope.

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
    dependent induction h ; [
      repeat eexists ; eassumption
    | destruct_pands ; mysplits ; try eassumption ;
      match goal with
      | h : nl ?A = _ |- _ =>
        solve [ transitivity (nl A) ; eauto ]
      end
    ]
  end.

Lemma inversionRel :
  forall {Σ Γ n T},
    Σ ;;; Γ |-i sRel n : T ->
    exists isdecl,
      let A := lift0 (S n) (safe_nth Γ (exist _ n isdecl)) in
      nl A = nl T.
Proof.
  invtac.
Defined.

Lemma inversionSort :
  forall {Σ Γ s T},
    Σ ;;; Γ |-i sSort s : T ->
    nl (sSort (Sorts.succ s)) = nl T.
Proof.
  invtac.
Defined.

Lemma inversionProd :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sProd n A B : T ->
    exists s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (nl (sSort (Sorts.prod_sort s1 s2)) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionLambda :
  forall {Σ Γ na A B t T},
    Σ ;;; Γ |-i sLambda na A B t : T ->
      exists s1 s2 na',
        (Σ ;;; Γ |-i A : sSort s1) /\
        (Σ ;;; Γ ,, A |-i B : sSort s2) /\
        (Σ ;;; Γ ,, A |-i t : B) /\
        (nl (sProd na' A B) = nl T).
Proof.
  invtac.
  Unshelve. constructor.
Defined.

Lemma inversionApp :
  forall {Σ Γ t A B u T},
    Σ ;;; Γ |-i sApp t A B u : T ->
    exists s1 s2 n,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (Σ ;;; Γ |-i t : sProd n A B) /\
      (Σ ;;; Γ |-i u : A) /\
      (nl (B{ 0 := u }) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionSum :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sSum n A B : T ->
    exists s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (nl (sSort (Sorts.sum_sort s1 s2)) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionPair :
  forall {Σ Γ A B u v T},
    Σ ;;; Γ |-i sPair A B u v : T ->
    exists n s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : B{ 0 := u }) /\
      (nl (sSum n A B) = nl T).
Proof.
  invtac.
  Unshelve. constructor.
Defined.

Lemma inversionPi1 :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-i sPi1 A B p : T ->
    exists n s1 s2,
      (Σ ;;; Γ |-i p : sSum n A B) /\
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (nl A = nl T).
Proof.
  invtac.
Defined.

Lemma inversionPi2 :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-i sPi2 A B p : T ->
    exists n s1 s2,
      (Σ ;;; Γ |-i p : sSum n A B) /\
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (nl (B{ 0 := sPi1 A B p }) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionEq :
  forall {Σ Γ A u v T},
    Σ ;;; Γ |-i sEq A u v : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : A) /\
      (nl (sSort (Sorts.eq_sort s)) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionRefl :
  forall {Σ Γ A u T},
    Σ ;;; Γ |-i sRefl A u : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (nl (sEq A u u) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionJ :
  forall {Σ Γ A u P w v p T},
    Σ ;;; Γ |-i sJ A u P w v p : T ->
    exists s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : A) /\
      (Σ ;;; Γ ,, A ,, (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2) /\
      (Σ ;;; Γ |-i p : sEq A u v) /\
      (Σ ;;; Γ |-i w : (P {1 := u}){0 := sRefl A u}) /\
      (nl (P{1 := v}{0 := p}) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionTransport :
  forall {Σ Γ A B p t T},
    Σ ;;; Γ |-i sTransport A B p t : T ->
    exists s,
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) /\
      (Σ ;;; Γ |-i t : A) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (nl B = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeq :
  forall {Σ Γ A B a b T},
    Σ ;;; Γ |-i sHeq A a B b : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i a : A) /\
      (Σ ;;; Γ |-i b : B) /\
      (nl (sSort s) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionPack :
  forall {Σ Γ A1 A2 T},
    Σ ;;; Γ |-i sPack A1 A2 : T ->
    exists s,
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (nl (sSort s) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeqToEq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqToEq p : T ->
    exists A u v s,
     (Σ ;;; Γ |-i p : sHeq A u A v) /\
     (Σ ;;; Γ |-i A : sSort s) /\
     (Σ ;;; Γ |-i u : A) /\
     (Σ ;;; Γ |-i v : A) /\
     (nl (sEq A u v) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeqRefl :
  forall {Σ Γ A a T},
    Σ ;;; Γ |-i sHeqRefl A a : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i a : A) /\
      (nl (sHeq A a A a) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeqSym :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqSym p : T ->
    exists A a B b s,
      (Σ ;;; Γ |-i p : sHeq A a B b) /\
      (Σ ;;; Γ |-i a : A) /\
      (Σ ;;; Γ |-i b : B) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (nl (sHeq B b A a) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeqTrans :
  forall {Σ Γ p q T},
    Σ ;;; Γ |-i sHeqTrans p q : T ->
    exists A a B b C c s,
      (Σ ;;; Γ |-i p : sHeq A a B b) /\
      (Σ ;;; Γ |-i q : sHeq B b C c) /\
      (Σ ;;; Γ |-i a : A) /\
      (Σ ;;; Γ |-i b : B) /\
      (Σ ;;; Γ |-i c : C) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i C : sSort s) /\
      (nl (sHeq A a C c) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeqTransport :
  forall {Σ Γ p t T},
    Σ ;;; Γ |-i sHeqTransport p t : T ->
    exists A B s,
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) /\
      (Σ ;;; Γ |-i t : A) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (nl (sHeq A t B (sTransport A B p t)) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionCongProd :
  forall {Σ Γ B1 B2 pA pB T},
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB : T ->
    exists s z nx ny A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (nl (sHeq (sSort (Sorts.prod_sort s z)) (sProd nx A1 B1)
                (sSort (Sorts.prod_sort s z)) (sProd ny A2 B2))
       = nl T).
Proof.
  invtac. Unshelve. all: constructor.
Defined.

Lemma inversionCongLambda :
  forall {Σ Γ B1 B2 t1 t2 pA pB pt T},
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt : T ->
    exists s z nx ny A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                    ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                    ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ ,, A1 |-i t1 : B1) /\
      (Σ ;;; Γ ,, A2 |-i t2 : B2) /\
      (nl (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                (sProd ny A2 B2) (sLambda ny A2 B2 t2))
       = nl T).
Proof.
  invtac. Unshelve. all: constructor.
Defined.

Lemma inversionCongApp :
  forall {Σ Γ B1 B2 pu pA pB pv T},
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv : T ->
    exists s z nx ny A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) /\
      (Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i u1 : sProd nx A1 B1) /\
      (Σ ;;; Γ |-i u2 : sProd ny A2 B2) /\
      (Σ ;;; Γ |-i v1 : A1) /\
      (Σ ;;; Γ |-i v2 : A2) /\
      (nl (sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                (B2{0 := v2}) (sApp u2 A2 B2 v2))
       = nl T).
Proof.
  invtac.
Defined.

Lemma inversionCongSum :
  forall {Σ Γ B1 B2 pA pB T},
    Σ ;;; Γ |-i sCongSum B1 B2 pA pB : T ->
    exists s z nx ny A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (nl (sHeq (sSort (Sorts.sum_sort s z)) (sSum nx A1 B1)
                (sSort (Sorts.sum_sort s z)) (sSum ny A2 B2))
       = nl T).
Proof.
  invtac. Unshelve. all: constructor.
Defined.

Lemma inversionCongPair :
  forall {Σ Γ B1 B2 pA pB pu pv T},
    Σ ;;; Γ |-i sCongPair B1 B2 pA pB pu pv : T ->
    exists s z nx ny A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) /\
      (Σ ;;; Γ |-i pv : sHeq (B1{ 0 := u1 }) v1 (B2{ 0 := u2 }) v2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i u1 : A1) /\
      (Σ ;;; Γ |-i u2 : A2) /\
      (Σ ;;; Γ |-i v1 : B1{ 0 := u1 }) /\
      (Σ ;;; Γ |-i v2 : B2{ 0 := u2 }) /\
      (nl (sHeq (sSum nx A1 B1) (sPair A1 B1 u1 v1)
                (sSum ny A2 B2) (sPair A2 B2 u2 v2))
       = nl T).
Proof.
  invtac. Unshelve. all: constructor.
Defined.

Lemma inversionCongPi1 :
  forall {Σ Γ B1 B2 pA pB pp T},
    Σ ;;; Γ |-i sCongPi1 B1 B2 pA pB pp : T ->
    exists s z nx ny A1 A2 p1 p2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i p1 : sSum nx A1 B1) /\
      (Σ ;;; Γ |-i p2 : sSum ny A2 B2) /\
      (nl (sHeq A1 (sPi1 A1 B1 p1) A2 (sPi1 A2 B2 p2)) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionCongPi2 :
  forall {Σ Γ B1 B2 pA pB pp T},
    Σ ;;; Γ |-i sCongPi2 B1 B2 pA pB pp : T ->
    exists s z nx ny A1 A2 p1 p2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i p1 : sSum nx A1 B1) /\
      (Σ ;;; Γ |-i p2 : sSum ny A2 B2) /\
      (nl (sHeq (B1{ 0 := sPi1 A1 B1 p1}) (sPi2 A1 B1 p1)
                (B2{ 0 := sPi1 A2 B2 p2}) (sPi2 A2 B2 p2))
       = nl T).
Proof.
  invtac.
Defined.

Lemma inversionCongEq :
  forall {Σ Γ pA pu pv T},
    Σ ;;; Γ |-i sCongEq pA pu pv : T ->
    exists s A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) /\
      (Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i u1 : A1) /\
      (Σ ;;; Γ |-i u2 : A2) /\
      (Σ ;;; Γ |-i v1 : A1) /\
      (Σ ;;; Γ |-i v2 : A2) /\
      (nl (sHeq (sSort (Sorts.eq_sort s)) (sEq A1 u1 v1)
            (sSort (Sorts.eq_sort s)) (sEq A2 u2 v2))
       = nl T).
Proof.
  invtac.
Defined.

Lemma inversionCongRefl :
  forall {Σ Γ pA pu T},
    Σ ;;; Γ |-i sCongRefl pA pu : T ->
    exists s A1 A2 u1 u2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i u1 : A1) /\
      (Σ ;;; Γ |-i u2 : A2) /\
      (nl (sHeq (sEq A1 u1 u1) (sRefl A1 u1)
                (sEq A2 u2 u2) (sRefl A2 u2))
       = nl T).
Proof.
  invtac.
Defined.

Lemma inversionEqToHeq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sEqToHeq p : T ->
    exists A u v s,
      (Σ ;;; Γ |-i p : sEq A u v) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : A) /\
      (nl (sHeq A u A v) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionHeqTypeEq :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-i sHeqTypeEq A B p : T ->
    exists u v s,
      (Σ ;;; Γ |-i p : sHeq A u B v) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : B) /\
      (nl (sEq (sSort s) A B) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionProjT1 :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjT1 p : T ->
    exists s A1 A2,
      (Σ ;;; Γ |-i p : sPack A1 A2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (nl A1 = nl T).
Proof.
  invtac.
Defined.

Lemma inversionProjT2 :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjT2 p : T ->
    exists s A1 A2,
      (Σ ;;; Γ |-i p : sPack A1 A2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (nl A2 = nl T).
Proof.
  invtac.
Defined.

Lemma inversionProjTe :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjTe p : T ->
    exists s A1 A2,
      (Σ ;;; Γ |-i p : sPack A1 A2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (nl (sHeq A1 (sProjT1 p) A2 (sProjT2 p)) = nl T).
Proof.
  invtac.
Defined.

Lemma inversionAx :
  forall {Σ Γ id T},
    Σ ;;; Γ |-i sAx id : T ->
    exists ty,
      (lookup_glob Σ id = Some ty) /\
      (nl ty = nl T).
Proof.
  invtac.
Defined.

End Inversions.

(* Tactic to apply inversion automatically *)

Open Scope i_scope.

Ltac ttinv h :=
  let s := fresh "s" in
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let z := fresh "z" in
  let his := fresh "is" in
  let nx := fresh "nx" in
  let ny := fresh "ny" in
  let np := fresh "np" in
  let ne := fresh "ne" in
  let na := fresh "na" in
  let A := fresh "A" in
  let B := fresh "B" in
  let C := fresh "C" in
  let A1 := fresh "A1" in
  let A2 := fresh "A2" in
  let B1 := fresh "B1" in
  let B2 := fresh "B2" in
  let u := fresh "u" in
  let v := fresh "v" in
  let u1 := fresh "u1" in
  let u2 := fresh "u2" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  let p1 := fresh "p1" in
  let p2 := fresh "p2" in
  let a := fresh "a" in
  let b := fresh "b" in
  let c := fresh "c" in
  let t := fresh "t" in
  let ty := fresh "ty" in
  let univs := fresh "univs" in
  let decl := fresh "decl" in
  let isdecl := fresh "isdecl" in
  let hh := fresh "h" in
  lazymatch type of h with
  | _ ;;; _ |-i ?term : _ =>
    lazymatch term with
    | sRel _ => destruct (inversionRel h) as [his hh]
    | sSort _ => pose proof (inversionSort h) as hh
    | sProd _ _ _ => destruct (inversionProd h) as (s1 & s2 & hh) ; splits_one hh
    | sLambda _ _ _ _ => destruct (inversionLambda h) as (s1 & s2 & na & hh) ;
                        splits_one hh
    | sApp _ _ _ _ => destruct (inversionApp h) as (s1 & s2 & na & hh) ;
                       splits_one hh
    | sSum _ _ _ => destruct (inversionSum h) as (s1 & s2 & hh) ; splits_one hh
    | sPair _ _ _ _ =>
      destruct (inversionPair h) as (nx & s1 & s2 & hh) ; splits_one hh
    | sPi1 _ _ _ =>
      destruct (inversionPi1 h) as (nx & s1 & s2 & hh) ; splits_one hh
    | sPi2 _ _ _ =>
      destruct (inversionPi2 h) as (nx & s1 & s2 & hh) ; splits_one hh
    | sEq _ _ _ => destruct (inversionEq h) as (s & hh) ; splits_one hh
    | sRefl _ _ => destruct (inversionRefl h) as (s & hh) ; splits_one hh
    | sJ _ _ _ _ _ _ => destruct (inversionJ h) as (s1 & s2 & hh) ;
                       splits_one hh
    | sTransport _ _ _ _ => destruct (inversionTransport h) as (s & hh) ;
                           splits_one hh
    | sHeq _ _ _ _ => destruct (inversionHeq h) as (s & hh) ; splits_one hh
    | sHeqToEq _ => destruct (inversionHeqToEq h) as (A & u & v & s & hh) ;
                   splits_one hh
    | sHeqRefl _ _ => destruct (inversionHeqRefl h) as (s & hh) ; splits_one hh
    | sHeqSym _ => destruct (inversionHeqSym h) as (A & a & B & b & s & hh) ;
                  splits_one hh
    | sHeqTrans _ _ =>
      destruct (inversionHeqTrans h) as (A & a & B & b & C & c & s & hh) ;
      splits_one hh
    | sHeqTransport _ _ =>
      destruct (inversionHeqTransport h) as (A & B & s & hh) ;
      splits_one hh
    | sCongProd _ _ _ _ =>
      destruct (inversionCongProd h) as (s & z & nx & ny & A1 & A2 & hh) ;
      splits_one hh
    | sCongLambda _ _ _ _ _ _ _ =>
      destruct (inversionCongLambda h)
        as (s & z & nx & ny & A1 & A2 & hh) ;
      splits_one hh
    | sCongApp _ _ _ _ _ _ =>
      destruct (inversionCongApp h)
        as (s & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongSum _ _ _ _ =>
      destruct (inversionCongSum h) as (s & z & nx & ny & A1 & A2 & hh) ;
      splits_one hh
    | sCongPair _ _ _ _ _ _ =>
      destruct (inversionCongPair h)
        as (s & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongPi1 _ _ _ _ _ =>
      destruct (inversionCongPi1 h)
        as (s & z & nx & ny & A1 & A2 & p1 & p2 & hh) ;
      splits_one hh
    | sCongPi2 _ _ _ _ _ =>
      destruct (inversionCongPi2 h)
        as (s & z & nx & ny & A1 & A2 & p1 & p2 & hh) ;
      splits_one hh
    | sCongEq _ _ _ =>
      destruct (inversionCongEq h) as (s & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongRefl _ _ =>
      destruct (inversionCongRefl h) as (s & A1 & A2 & u1 & u2 & hh) ;
      splits_one hh
    | sEqToHeq _ =>
      destruct (inversionEqToHeq h) as (A & u & v & s & hh) ;
      splits_one hh
    | sHeqTypeEq _ _ _ =>
      destruct (inversionHeqTypeEq h) as (u & v & s & hh) ;
      splits_one hh
    | sPack _ _ => destruct (inversionPack h) as (s & hh) ; splits_one hh
    | sProjT1 _ =>
      destruct (inversionProjT1 h) as (s & A1 & A2 & hh) ; splits_one hh
    | sProjT2 _ =>
      destruct (inversionProjT2 h) as (s & A1 & A2 & hh) ; splits_one hh
    | sProjTe _ =>
      destruct (inversionProjTe h) as (s & A1 & A2 & hh) ; splits_one hh
    | sAx _ => destruct (inversionAx h) as [ty hh] ; splits_one hh
    end
  end.
