(*
  The purpose of this file is to write more complex examples.
  Or rather to automate examples more.

  Ideally the procedure should take an ITT definition
  (using the candidate axiom) and produce on its own the context
  as well as the obligations.
  This means writing ITT and ETT checkers as Coq terms rather than in Ltac.
*)

Require Import TypingFlags.Loader.
Set Type In Type.

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import All.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
ITypingAdmissible DecideConversion XTyping Quotes Translation FinalTranslation
FullQuote ExampleQuotes ExamplesUtil XTypingLemmata IChecking XChecking.
Import MonadNotation.

Open Scope string_scope.
Open Scope x_scope.

Module I := ITyping.

(* First we write an ITT checker that will not generate any obligation.
   It will be proven sound but not complete.
   Since ITT derivations are proof-irrelevant, it needs only return a boolean.
 *)
Fixpoint ittcheck (fuel : nat) (Σ : sglobal_context) (Γ : scontext) (t : sterm) (A : sterm) {struct t} : bool :=
  match t with
  | sRel n =>
    match nth_error Γ n with
    | Some B => isconv fuel (lift0 (S n) B) A
    | None => false
    end
  | _ => false
  end.

Lemma ittcheck_sound :
  forall fuel Σ Γ t A s,
    ittcheck fuel Σ Γ t A = true ->
    I.wf Σ Γ ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i t : A.
Proof.
  intros fuel Σ Γ t A s h hΓ hA.
  revert fuel Σ Γ A s h hΓ hA.
  induction t ; intros fuel Σ Γ A z h hΓ hA.
  all: try (cbn in h ; discriminate h).
  - cbn in h. revert h. case_eq (nth_error Γ n).
    + intros B eq h.
      eapply I.type_conv.
      * eapply I.type_Rel. assumption.
      * eassumption.
      * eapply isconv_sound. erewrite nth_error_Some_safe_nth with (e := eq).
        eassumption.
    + intros _ bot. discriminate bot.
Qed.