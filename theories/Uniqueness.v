(* Uniqueness of Typing *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
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

Ltac nleq :=
  repeat (try eapply nl_lift ; try eapply nl_subst) ;
  cbn ; auto ; f_equal ; eauto.

Ltac finish :=
  lazymatch goal with
  | h : nl ?u = nl ?t |- _ = nl ?t =>
    transitivity (nl u) ; [ | assumption ] ;
    repeat nleq
  end.

Ltac reunih :=
  match goal with
  | ih : _ -> _ -> _ -> _ ;;; _ |-i ?t : _ -> _ ;;; _ |-i ?t : _ -> _,
    h1 : ?Σ ;;; ?Γ |-i ?t : _,
    h2 : _ ;;; _ |-i ?t : ?A
    |- _ =>
    let hh2 := fresh h2 in
    assert (Σ ;;; Γ |-i t : A) as hh2 ; [
      eapply rename_typed ; try eassumption ; try reflexivity
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
    nl A = nl B.
Proof.
  intros Σ Γ A B u hg h1 h2.
  revert Γ A B h1 h2.
  induction u ; intros Γ A B h1 h2.
  all: try unitac h1 h2.
  all: try assumption.
  all: try solve [finish].
  - cbn in *. erewrite @safe_nth_irr with (isdecl' := is) in h0.
    assumption.
  - reunih.
    + cbn. f_equal. eauto.
    + repeat eapply wf_snoc.
      * eapply typing_wf. eassumption.
      * eassumption.
    + try assumption. try solve [finish].
  - reunih.
    + cbn. f_equal. eauto.
    + repeat eapply wf_snoc.
      * eapply typing_wf. eassumption.
      * eassumption.
    + try assumption. try solve [finish].
  - reunih.
    + cbn. f_equal. eauto.
    + repeat eapply wf_snoc.
      * eapply typing_wf. eassumption.
      * eassumption.
    + try assumption. try solve [finish].
  - rewrite h4 in h0. inversion h0. inversion h0. subst. assumption.
Defined.

End Uniqueness.