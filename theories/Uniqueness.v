(* Uniqueness of Typing *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From Equations Require Import Equations.
From Translation
Require Import util SAst SLiftSubst Equality SCommon ITyping
               ITypingInversions ITypingLemmata.

Section Uniqueness.

Context `{Sort_notion : Sorts.notion}.

(* Ltac nlassumption := *)
(*   try eapply (f_equal nl) ; assumption. *)

(* Ltac nleassumption := *)
(*   try eapply (f_equal nl) ; eassumption. *)

Ltac unih :=
  match goal with
  | ih : _ -> _ -> _ -> _ ;;; _ |-i ?t : _ -> _ ;;; _ |-i ?t : _ -> _,
    h1 : _ ;;; _ |-i ?t : _,
    h2 : _ ;;; _ |-i ?t : _
    |- _ =>
    specialize (ih _ _ _ h1 h2) ;
    simpl in ih ;
    inversion ih ; subst ; clear ih
  end.

Ltac unitac h1 h2 :=
  ttinv h1 ; ttinv h2 ;
  eapply eq_trans ; [
    eapply eq_sym ; eassumption
  | repeat unih
  ].

Ltac finish :=
  lazymatch goal with
  | h : ?u = ?t |- _ = ?t =>
    transitivity u ; [ | assumption ] ;
    reflexivity
  end.

Ltac reunih :=
  match goal with
  | ih : _ -> _ -> _ -> _ ;;; _ |-i ?t : _ -> _ ;;; _ |-i ?t : _ -> _,
    h1 : ?Σ ;;; ?Γ |-i ?t : _,
    h2 : _ ;;; _ |-i ?t : ?A
    |- _ =>
    let hh2 := fresh h2 in
    assert (Σ ;;; Γ |-i t : A) as hh2 ; [
      eapply meta_conv ; try eassumption ; try reflexivity
    | specialize (ih _ _ _ h1 hh2) ;
      simpl in ih ;
      inversion ih ; subst ; clear ih
    ]
  end.

Lemma uniqueness :
  forall {Σ Γ A B u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    A = B.
Proof.
  intros Σ Γ A B u hg h1 h2.
  revert Γ A B h1 h2.
  induction u ; intros Γ A B h1 h2.
  all: try unitac h1 h2.
  all: try assumption.
  all: try reflexivity.
  - rewrite H1 in H. inversion H. subst. reflexivity.
  - rewrite h4 in h0. inversion h0. subst. reflexivity.
Defined.

End Uniqueness.