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
ITypingAdmissible DecideConversion XTyping Quotes Translation FundamentalLemma
FinalTranslation FullQuote ExampleQuotes ExamplesUtil XTypingLemmata IChecking
XChecking Equality.
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
  | sPair A B u v =>
    _ittcheck fuel Σ Γ u A &&
    _ittcheck fuel Σ Γ v (B{0 := u}) &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,,A) B Ty &&
    isconv fuel (sSum nAnon A B) T
  | sPi1 A B p =>
    _ittcheck fuel Σ Γ p (sSum nAnon A B) &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,,A) B Ty &&
    isconv fuel A T
  | sPi2 A B p =>
    _ittcheck fuel Σ Γ p (sSum nAnon A B) &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,,A) B Ty &&
    isconv fuel (B{0 := sPi1 A B p}) T
  | sEq A u v =>
    _ittcheck fuel Σ Γ u A &&
    _ittcheck fuel Σ Γ v A &&
    _ittcheck fuel Σ Γ A Ty &&
    isconv fuel Ty T
  | sRefl A u =>
    _ittcheck fuel Σ Γ u A &&
    _ittcheck fuel Σ Γ A Ty &&
    isconv fuel (sEq A u u) T
  | sAx id =>
    match lookup_glob Σ id with
    | Some A => isconv fuel A T
    | None => false
    end
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
  - repeat destruct_andb.
    eapply I.type_conv.
    + assert (Σ ;;; Γ |-i t1 : Ty).
      { eapply IHt1 ; try eassumption.
        constructor. assumption.
      }
      assert (I.wf Σ (Γ,, t1)).
      { econstructor ; eassumption. }
      eapply type_Pair' ; try assumption.
      * eapply IHt3 ; eassumption.
      * eapply IHt4 ; try eassumption.
        lift_sort. eapply ITypingLemmata.typing_subst ; try eassumption.
        -- eapply IHt2 ; try eassumption.
           constructor. assumption.
        -- eapply IHt3 ; eassumption.
      * eapply IHt2 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + assert (Σ ;;; Γ |-i t1 : Ty).
      { eapply IHt1 ; try eassumption.
        constructor. assumption.
      }
      assert (I.wf Σ (Γ,, t1)).
      { econstructor ; eassumption. }
      eapply type_Pi1' ; try assumption.
      eapply IHt3 ; try eassumption.
      eapply type_Sum' ; try eassumption.
      intro. eapply IHt2 ; try eassumption.
      constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + assert (Σ ;;; Γ |-i t1 : Ty).
      { eapply IHt1 ; try eassumption.
        constructor. assumption.
      }
      assert (I.wf Σ (Γ,, t1)).
      { econstructor ; eassumption. }
      eapply type_Pi2' ; try assumption.
      eapply IHt3 ; try eassumption.
      eapply type_Sum' ; try eassumption.
      intro. eapply IHt2 ; try eassumption.
      constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Eq' ; try assumption.
      * eapply IHt2 ; try eassumption.
        eapply IHt1 ; try eassumption.
        constructor. assumption.
      * eapply IHt3 ; try eassumption.
        eapply IHt1 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Refl' ; try assumption.
      eapply IHt2 ; try eassumption.
      eapply IHt1 ; try eassumption.
      constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - revert h.
    case_eq (lookup_glob Σ id).
    + intros T eq h.
      eapply I.type_conv.
      * eapply I.type_Ax ; eassumption.
      * eassumption.
      * eapply isconv_sound. eassumption.
    + intros _ bot. discriminate bot.
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

Open Scope list_scope.

(*
  For ETT we want to be able to build the derivation constructively
  and we should be able to get a set of obligations from it.

  ettconv generates a list (actually none or one) of obligations
  that are necessary to entail the conversion.

  _ettcheck returns either a list of obligations or an error (None)
*)
Definition ettconv Γ A B : list sterm :=
  if eq_term A B
  then []
  else [ Prods Γ (sEq Ty A B) ].

Fixpoint _ettcheck (Σ : sglobal_context) (Γ : scontext) (t : sterm)
                  (T : sterm) {struct t} : option (list sterm) :=
  match t with
  | sRel n =>
    B <- nth_error Γ n ;;
    ret (ettconv Γ (lift0 (S n) B) T)
  | sSort _ => ret (ettconv Γ Ty T)
  | sProd n A B =>
    ob1 <- _ettcheck Σ Γ A Ty ;;
    ob2 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ret (ob1 ++ ob2 ++ ettconv Γ Ty T)
  | sLambda n A B t =>
    ob1 <- _ettcheck Σ (Γ,, A) t B ;;
    ob2 <- _ettcheck Σ Γ A Ty ;;
    ob3 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ret (ob1 ++ ob2 ++ ob3 ++ ettconv Γ (sProd n A B) T)
  | sApp u A B v =>
    ob1 <- _ettcheck Σ Γ u (sProd nAnon A B) ;;
    ob2 <- _ettcheck Σ Γ v A ;;
    ob3 <- _ettcheck Σ Γ A Ty ;;
    ob4 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ret (ob1 ++ ob2 ++ ob3 ++ ob4 ++ ettconv Γ (B{0 := v}) T)
  | sSum n A B =>
    ob1 <- _ettcheck Σ Γ A Ty ;;
    ob2 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ret (ob1 ++ ob2 ++ ettconv Γ Ty T)
  | sPair A B u v =>
    ob1 <- _ettcheck Σ Γ u A ;;
    ob2 <- _ettcheck Σ Γ v (B{0 := u}) ;;
    ob3 <- _ettcheck Σ Γ A Ty ;;
    ob4 <- _ettcheck Σ (Γ,,A) B Ty ;;
    ret (ob1 ++ ob2 ++ ob3 ++ ob4 ++ ettconv Γ (sSum nAnon A B) T)
  | sPi1 A B p =>
    ob1 <- _ettcheck Σ Γ p (sSum nAnon A B) ;;
    ob2 <- _ettcheck Σ Γ A Ty ;;
    ob3 <- _ettcheck Σ (Γ,,A) B Ty ;;
    ret (ob1 ++ ob2 ++ ob3 ++ ettconv Γ A T)
  | sPi2 A B p =>
    ob1 <- _ettcheck Σ Γ p (sSum nAnon A B) ;;
    ob2 <- _ettcheck Σ Γ A Ty ;;
    ob3 <- _ettcheck Σ (Γ,,A) B Ty ;;
    ret (ob1 ++ ob2 ++ ob3 ++ ettconv Γ (B{0 := sPi1 A B p}) T)
  | sEq A u v =>
    ob1 <- _ettcheck Σ Γ u A ;;
    ob2 <- _ettcheck Σ Γ v A ;;
    ob3 <- _ettcheck Σ Γ A Ty ;;
    ret (ob1 ++ ob2 ++ ob3 ++ ettconv Γ Ty T)
  | sRefl A u =>
    ob1 <- _ettcheck Σ Γ u A ;;
    ob2 <- _ettcheck Σ Γ A Ty ;;
    ret (ob1 ++ ob2 ++ ettconv Γ (sEq A u u) T)
  | sAx id =>
    A <- lookup_glob Σ id ;;
    ret (ettconv Γ A T)
  | _ => None
  end.

Notation "s @ t" := (s ++ t)%string (right associativity, at level 60).

(* For the soundness lemma, we need to write an extend function that takes
   a global context and a list of obligations and put them together using a
   base name for the obligations.
 *)
Fixpoint extendi i (Σ : sglobal_context) name l : sglobal_context :=
  match l with
  | A :: l =>
    extendi (S i) (decl (name @ string_of_nat i) A :: Σ) name l
  | [] => Σ
  end.

Lemma extendi_cons :
  forall {i Σ name A l},
    extendi i Σ name (A :: l) =
    extendi (S i) (decl (name @ string_of_nat i) A :: Σ) name l.
Proof.
  reflexivity.
Defined.

Notation extend := (extendi 0).

Open Scope nat_scope.

Lemma lookup_extendi :
  forall {Σ name A obb obe i},
    let Σ' := extendi i Σ name (obb ++ (A :: obe)) in
    lookup_glob Σ' (name @ string_of_nat (i + #|obb|)) = Some A.
Proof.
  intros Σ name A obb obe i Σ'.
  revert Σ A obe i Σ'. induction obb as [| B obb ih ].
  - intros Σ A obe i Σ'. cbn in Σ'. cbn. admit.
  - intros Σ A obe i Σ'.
    unfold Σ'. rewrite <- app_comm_cons. rewrite extendi_cons.
    cbn. replace (i + S #|obb|) with (S i + #|obb|) by myomega.
    eapply ih.
Admitted.

Lemma lookup_extend :
  forall {Σ name A obb obe},
    let Σ' := extend Σ name (obb ++ (A :: obe)) in
    lookup_glob Σ' (name @ string_of_nat #|obb|) = Some A.
Proof.
  intros Σ name A obb obe Σ'.
  eapply (lookup_extendi (i := 0)).
Defined.

Lemma _ettcheck_sound :
  forall Σ Γ t A ob name obb obe,
    _ettcheck Σ Γ t A = Some ob ->
    let Σ' := extend Σ name (obb ,,, ob ,,, obe) in
    xtype_glob Σ' ->
    wf Σ' Γ ->
    Σ' ;;; Γ |-x A : Ty ->
    Σ' ;;; Γ |-x t : A.
Proof.
  intros Σ Γ t A ob name obb obe h Σ' hg hw hA.
  revert Σ Γ A ob name obb obe h Σ' hg hw hA.
  induction t ; intros Σ Γ A ob name obb obe h Σ' hg hw hA.
  all: try discriminate h.
  - cbn in h. revert h. case_eq (nth_error Γ n).
    + intros B eq.
      unfold ettconv. case_eq (eq_term (lift0 (S n) B) A).
      * intros eq' h. eapply type_conv.
        -- eapply type_Rel.
        -- eassumption.
        -- erewrite nth_error_Some_safe_nth with (e := eq).
           eapply eq_symmetry. eapply eq_alpha ; try assumption.
           symmetry. eapply eq_term_spec. assumption.
      * intros _ h. inversion h. subst. clear h. cbn in Σ'.
        eapply type_conv.
        -- eapply type_Rel.
        -- eassumption.
        -- erewrite nth_error_Some_safe_nth with (e := eq).
           eapply reflection. eapply close_goal ; try eassumption.
           (* Now we need to pick the right number and prove some lemma *)
           instantiate (1 := sAx (name ++ "0")).
           eapply type_Ax. cbn.
           destruct (ident_eq_spec (name ++ "0") (name ++ "0")).
           ++ reflexivity.
           ++ exfalso. auto.
    + intros _ bot. discriminate bot.
  - simpl in h. destruct s.
    eapply type_conv.
    + eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in h. revert h.
      case_eq (eq_term Ty A).
      * intros eq h. eapply eq_alpha.
        -- eapply eq_term_spec. assumption.
        -- constructor.
      * intros _ h. inversion h. subst. clear h. cbn in Σ'.
        set (na := name ++ "0") in *.
        eapply reflection. eapply close_goal ; try eassumption.
        instantiate (1 := sAx na).
        eapply type_Ax. cbn.
        destruct (ident_eq_spec na na).
        -- reflexivity.
        -- exfalso. auto.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 Ty).
    + intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty).
      * intros ob2 eq2 h.
        eapply type_conv.
        -- eapply xtype_Prod'.
           ++ assumption.
           ++ eapply IHt1.
              (* Either we need to change the theorem slightly,
                 or we need to use some weakening properties regarding
                 global context. Problem: it needs to take into account
                 interleaving.
               *)
Abort.
