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

   TODO Actually we could write infer directly.

   TODO The fact that we require the hyp on the type forces us to check
   it anyway when it could be simpler...
 *)
Fixpoint _ittcheck (fuel : nat) (Σ : sglobal_context) (Γ : scontext) (t : sterm)
                  (T : sterm) {struct t} : bool :=
  match t with
  | sRel n =>
    match nth_error Γ n with
    | Some B => isconv fuel (lift0 (S n) B) T
    | None => false
    end
  | sSort _ => isconv fuel Ty T
  | sProd n A B =>
    isconv fuel Ty T &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty
  | sLambda n A B t =>
    _ittcheck fuel Σ (Γ,, A) t B &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty &&
    isconv fuel (sProd n A B) T
  | sApp u A B v =>
    _ittcheck fuel Σ Γ u (sProd nAnon A B) &&
    _ittcheck fuel Σ Γ v A &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty &&
    isconv fuel (B{0 := v}) T
  | sSum n A B =>
    isconv fuel Ty T &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty
  | _ => false
  end.

Lemma _ittcheck_sound :
  forall fuel Σ Γ t A,
    _ittcheck fuel Σ Γ t A = true ->
    type_glob Σ ->
    I.wf Σ Γ ->
    Σ ;;; Γ |-i A : Ty ->
    Σ ;;; Γ |-i t : A.
Proof.
  intros fuel Σ Γ t A h hg hΓ hA.
  revert fuel Γ A h hΓ hA.
  induction t ; intros fuel Γ A h hΓ hA.
  all: cbn in h.
  all: try discriminate h.
  - revert h. case_eq (nth_error Γ n).
    + intros B eq h.
      eapply I.type_conv.
      * eapply I.type_Rel. assumption.
      * eassumption.
      * eapply isconv_sound. erewrite nth_error_Some_safe_nth with (e := eq).
        eassumption.
    + intros _ bot. discriminate bot.
  - destruct s. eapply I.type_conv.
    + econstructor. assumption.
    + eassumption.
    + cbn. eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    assert (Σ;;; Γ |-i t1 : Ty).
    { eapply IHt1 ; try eassumption.
      econstructor. assumption.
    }
    assert (I.wf Σ (Γ,, t1)).
    { econstructor ; eassumption. }
    eapply I.type_conv.
    + econstructor ; try eassumption.
      eapply IHt2 ; try eassumption.
      econstructor. assumption.
    + eassumption.
    + cbn. eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Lambda' ; try assumption.
      * eapply IHt1 ; try eassumption.
        econstructor. assumption.
      * intro hΓ'. eapply IHt3 ; try eassumption.
        eapply IHt2 ; try eassumption.
        econstructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_App' ; try eassumption.
      * eapply IHt1 ; try eassumption.
        eapply type_Prod'.
        -- eapply IHt2 ; try eassumption.
           constructor. assumption.
        -- intro. eapply IHt3 ; try eassumption.
           constructor. assumption.
      * eapply IHt4 ; try eassumption.
        eapply IHt2 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Sum'.
      * eapply IHt1 ; try eassumption.
        constructor. assumption.
      * intro. eapply IHt2 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
Qed.

Definition ittcheck (fuel : nat) (Σ : sglobal_context) (Γ : scontext) (t : sterm)
           (T : sterm) : bool :=
  _ittcheck fuel Σ Γ T Ty && _ittcheck fuel Σ Γ t T.

Lemma ittcheck_sound :
  forall fuel Σ Γ t A,
    ittcheck fuel Σ Γ t A = true ->
    type_glob Σ ->
    I.wf Σ Γ ->
    Σ ;;; Γ |-i t : A.
Proof.
  intros fuel Σ Γ t A h hg hw.
  unfold ittcheck in h.
  destruct_andb.
  eapply _ittcheck_sound ; try eassumption.
  eapply _ittcheck_sound ; try eassumption.
  econstructor. assumption.
Qed.