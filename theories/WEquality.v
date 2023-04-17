From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From Equations Require Import Equations.
From Translation Require Import util Sorts WAst WLiftSubst.

Section Equality.

Context `{Sort_notion : Sorts.notion}.

(* Equality between terms *)

Section dec.

  Ltac finish :=
    let h := fresh "h" in
    right ;
    match goal with
    | e : ?t <> ?u |- _ =>
      intro h ; apply e ; now inversion h
    end.

  Ltac fcase c :=
    let e := fresh "e" in
    case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

  Ltac eq_term_dec_tac eq_term_dec :=
    repeat match goal with
           | t : wterm, u : wterm |- _ => fcase (eq_term_dec t u)
           | s : sort, z : sort |- _ => fcase (Sorts.eq_dec s z)
           | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
           | i : ident, i' : ident |- _ => fcase (string_dec i i')
           end.

  Fixpoint eq_term_dec (t u : wterm) : { t = u } + { t <> u }.
  Proof.
    destruct t ; destruct u ; try (right ; discriminate).
    all: eq_term_dec_tac eq_term_dec.
  Defined.

End dec.

Definition eq_term (t u : wterm) : bool :=
  if eq_term_dec t u then true else false.

Lemma eq_term_spec :
  forall {t u},
    eq_term t u = true <-> t = u.
Proof.
  intros t u. split.
  - unfold eq_term. case (eq_term_dec t u).
    + intros. assumption.
    + intros. discriminate.
  - unfold eq_term. case (eq_term_dec t u).
    + reflexivity.
    + intros h e. exfalso. apply h. apply e.
Defined.

Fact eq_term_refl :
  forall {t}, eq_term t t = true.
Proof.
  intro t. unfold eq_term.
  case (eq_term_dec t t).
  - intro. reflexivity.
  - intro h. exfalso. apply h. reflexivity.
Defined.

Fact eq_term_sym :
  forall {t u}, eq_term t u = true -> eq_term u t = true.
Proof.
  unfold eq_term.
  intros t u.
  case (eq_term_dec u t) ; intro e.
  - reflexivity.
  - case (eq_term_dec t u) ; intro e'.
    + exfalso. apply e. easy.
    + intro. easy.
Defined.

Fact eq_term_trans :
  forall {t u v}, eq_term t u = true -> eq_term u v = true -> eq_term t v = true.
Proof.
  intros t u v.
  unfold eq_term.
  case (eq_term_dec t u) ; intro e1.
  - intros _. rewrite e1. auto.
  - discriminate.
Defined.

Lemma eq_term_lift :
  forall {t u n k},
    eq_term t u = true ->
    eq_term (lift n k t) (lift n k u) = true.
Proof.
  intros t u n k h. apply eq_term_spec in h.
  apply eq_term_spec.
  f_equal. assumption.
Defined.

Lemma eq_term_subst :
  forall {t t' u u' n},
    eq_term t t' = true ->
    eq_term u u' = true ->
    eq_term (t{n := u}) (t'{n := u'}) = true.
Proof.
  intros t t' u u' n ht hu.
  apply eq_term_spec in ht.
  apply eq_term_spec in hu.
  apply eq_term_spec.
  f_equal. all: assumption.
Defined.

End Equality.
