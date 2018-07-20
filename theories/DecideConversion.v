(* (Semi-)Decide conversion in ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata ContextConversion Uniqueness.

Section Decide.

  Context `{Sort_notion : Sorts.notion}.

  (* Returns [Some t'] such that [Σ |-i t ▷ t'], or [None] if it cannot be
     reduced.
     Not really applying any strategy except going deeply in the terms.
   *)
  Fixpoint reduce1 (t : sterm) : option sterm :=
    match t with
    | sProd n A B =>
      match reduce1 A with
      | Some A' => Some (sProd n A' B)
      | None =>
        match reduce1 B with
        | Some B' => Some (sProd n A B')
        | None => None
        end
      end
    | sLambda n A B t =>
      match reduce1 A with
      | Some A' => Some (sLambda n A' B t)
      | None =>
        match reduce1 B with
        | Some B' => Some (sLambda n A B' t)
        | None =>
          match reduce1 t with
          | Some t' => Some (sLambda n A B t')
          | None => None
          end
        end
      end
    | _ => None
    end.

  Lemma reduce1_sound :
    forall {Σ t u},
      reduce1 t = Some u ->
      Σ |-i t ▷ u.
  Proof.
    intros Σ t u h. revert u h.
    induction t ; intros u h.
    all: try (cbn in h ; discriminate h).
    - revert h. cbn. case_eq (reduce1 t1).
      + intros A' hA h. inversion h. subst. clear h.
        constructor. auto.
      + intros _. case_eq (reduce1 t2).
        * intros B' hB h. inversion h. subst. clear h.
          constructor. auto.
        * intros _. discriminate.
    - revert h. cbn.
  Admitted.

  (* Fixpoint isconv (fuel : nat) (u v : sterm) {struct fuel} : bool := *)
  (*   match fuel with *)
  (*   | 0 => false *)
  (*   | S fuel => *)
  (*     eq_term u v || *)
  (*     match  *)
  (*   end. *)

End Decide.