(* (Semi-)Decide conversion in ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata ContextConversion Uniqueness.

Section Decide.

  Context `{Sort_notion : Sorts.notion}.

  Definition get_or {A B} (x : option A) (get : A -> B) (or : option B) : option B :=
    match x with
    | Some a => Some (get a)
    | None => or
    end.

  Notation "x '>>' a '==>' e '--' b" := 
    (get_or x (fun a => e) b) (at level 100, e at next level, right associativity).

  (* Returns [Some t'] such that [Σ |-i t ▷ t'], or [None] if it cannot be
     reduced.
     Not really applying any strategy except going deeply in the terms.
   *)
  Fixpoint reduce1 (t : sterm) {struct t} : option sterm :=
    match t with
    | sProd n A B =>
      reduce1 A >> A' ==> sProd n A' B --
      reduce1 B >> B' ==> sProd n A B' --
      None
    | sLambda n A B t =>
      reduce1 A >> A' ==> sLambda n A' B t --
      reduce1 B >> B' ==> sLambda n A B' t --
      reduce1 t >> t' ==> sLambda n A B t' --
      None
    | _ => None
    end.

  Ltac one_case :=
    lazymatch goal with
    | |- (?d >> _ ==> _ -- _) = _ -> _ =>
      case_eq d ; [
        intros ? ? h ; inversion h ; subst ; clear h ;
        constructor ; solve [ auto ]
      | intros _ ; cbn
      ]
    end.

  Lemma reduce1_sound :
    forall {Σ t u},
      reduce1 t = Some u ->
      Σ |-i t ▷ u.
  Proof.
    intros Σ t u h. revert u h.
    induction t ; intros u h.
    all: try (cbn in h ; discriminate h).
    - revert h. cbn. repeat one_case. discriminate.
    - revert h. cbn. repeat one_case. discriminate.
  Defined.

  (* When it returns [true], we have [Σ |-i u = v].
     It compares the terms first by alpha-conversion, and then reduces the
     first one as much as possible, then the second one.
   *)
  Fixpoint isconv (fuel : nat) (u v : sterm) {struct fuel} : bool :=
    match fuel with
    | 0 => false
    | S fuel =>
      eq_term u v ||
      match reduce1 u with
      | Some u' => isconv fuel u' v
      | None =>
        match reduce1 v with
        | Some v' => isconv fuel u v'
        | None => false
        end
      end
    end.

  Lemma isconv_sound :
    forall {Σ fuel u v},
      isconv fuel u v = true ->
      Σ |-i u = v.
  Proof.
    intros Σ fuel u v h. revert u v h.
    induction fuel ; intros u v h ; try discriminate h.
    cbn in h. apply orb_prop in h. destruct h as [h | h].
    - constructor. unfold eq_term in h.
      destruct (nl_dec (nl u) (nl v)).
      + assumption.
      + discriminate.
    - revert h. case_eq (reduce1 u).
      + intros u' hu h. eapply conv_red_l.
        * eapply reduce1_sound. eassumption.
        * eapply IHfuel. assumption.
      + intros _. case_eq (reduce1 v).
        * intros v' hv h. eapply conv_red_r.
          -- eapply IHfuel. eassumption.
          -- eapply reduce1_sound. assumption.
        * intros _. discriminate.
  Defined.

End Decide.