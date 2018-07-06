(*! General utilities to build ETT derivations *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import utils Ast LiftSubst Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible XTyping
     FundamentalLemma Translation FinalTranslation FullQuote ExampleQuotes
     XTypingLemmata ExamplesUtil.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

Lemma type_conv'' :
  forall {Γ t A B s},
    Σi ;;; Γ |-x t : A ->
    Σi ;;; Γ |-x A = B : sSort s ->
    Σi ;;; Γ |-x B : sSort s ->
    Σi ;;; Γ |-x t : B.
Proof.
  intros Γ t A B s H H0 H1.
  eapply type_conv ; eassumption.
Defined.


Lemma xtype_Prod' :
  forall {Σ Γ n A B},
    Σ ;;; Γ |-x A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : Ty) ->
    Σ ;;; Γ |-x sProd n A B : Ty.
Proof.
  intros Σ Γ n A B hA hB.
  eapply meta_conv.
  - eapply type_Prod.
    + eassumption.
    + apply hB. econstructor ; try eassumption.
      eapply typing_wf. eassumption.
  - reflexivity.
Defined.

Lemma xtype_Lambda' :
  forall {Σ Γ n n' A B t},
    type_glob Σ ->
    xtype_glob Σ ->
    Σ ;;; Γ |-x A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x t : B) ->
    Σ ;;; Γ |-x sLambda n A B t : sProd n' A B.
Proof.
  intros Σ Γ n n' A B t hg xhg hA ht.
  assert (hw : wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply typing_wf. eassumption.
  }
  specialize (ht hw).
  destruct (istype_type hg xhg ht) as [[] hB].
  eapply type_Lambda ; eassumption.
Defined.

Lemma xtype_App' :
  forall {Σ Γ n t A B u},
    type_glob Σ ->
    xtype_glob Σ ->
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : Ty) ->
    Σ ;;; Γ |-x sApp t A B u : (B{0 := u})%s.
Proof.
  intros Σ Γ n t A B u hg xhg ht hu hB.
  destruct (istype_type hg xhg hu) as [[] hA].
  assert (hw : wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply typing_wf. eassumption.
  }
  specialize (hB hw).
  (* We need inversion of typing on ETT *)
  eapply type_App ; eassumption.
Defined.

Lemma xtype_Sum' :
  forall {Σ Γ n A B},
    Σ ;;; Γ |-x A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : Ty) ->
    Σ ;;; Γ |-x sSum n A B : Ty.
Proof.
  intros Σ Γ n A B hA hB.
  eapply meta_conv.
  - eapply type_Sum.
    + eassumption.
    + apply hB. econstructor ; try eassumption.
      eapply typing_wf. eassumption.
  - reflexivity.
Defined.

Lemma xtype_Eq' :
  forall {Σ Γ A u v},
    type_glob Σ ->
    xtype_glob Σ ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : A ->
    Σ ;;; Γ |-x sEq A u v : Ty.
Proof.
  intros Σ Γ A u v hg xhg hu hv.
  destruct (istype_type hg xhg hu) as [[] hA].
  eapply meta_conv.
  - eapply type_Eq ; eassumption.
  - reflexivity.
Defined.

Lemma xtype_Refl' :
  forall {Σ Γ A u},
    type_glob Σ ->
    xtype_glob Σ ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u hg xhg hu.
  destruct (istype_type hg xhg hu) as [[] hA].
  eapply type_Refl ; eassumption.
Defined.

Lemma xtype_Sort' :
  forall {Σ Γ},
    wf Σ Γ ->
    Σ ;;; Γ |-x Ty : Ty.
Proof.
  intros Σ Γ h.
  eapply meta_conv.
  - eapply type_Sort. assumption.
  - reflexivity.
Defined.

Lemma xwf_snoc' :
  forall {Σ Γ A},
    Σ ;;; Γ |-x A : Ty ->
    wf Σ (Γ ,, A).
Proof.
  intros Σ Γ A h.
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Lemma xtype_glob_cons' :
  forall {Σ d},
    xtype_glob Σ ->
    fresh_glob (dname d) Σ ->
    (xtype_glob Σ -> isType Σ [] (dtype d)) ->
    xtype_glob (d :: Σ).
Proof.
  intros Σ d hg hf hd.
  specialize (hd hg).
  econstructor ; eassumption.
Defined.

Ltac xglob :=
  first [
    eapply xtype_glob_nil
  | eapply xtype_glob_cons' ; [
      idtac
    | repeat (lazy ; econstructor) ; lazy ; try discriminate
    | intro ; eexists
    ]
  ].

Ltac ettintro :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-x ?t : ?T =>
    lazymatch t with
    | sRel ?n => refine (type_Rel _ _ n _ _)
    | sSort _ => eapply xtype_Sort'
    | sProd _ _ _ => eapply xtype_Prod' ; [| intro ]
    | sLambda _ _ _ _ => eapply xtype_Lambda' ; [ .. | intro ]
    | sApp _ _ _ _ => eapply xtype_App' ; [ .. | intro ]
    | sSum _ _ _ => eapply xtype_Sum' ; [| intro ]
    | sPair _ _ _ _ => eapply type_Pair
    | sPi1 _ _ _ => eapply type_Pi1
    | sPi2 _ _ _ => eapply type_Pi2
    | sEq _ _ _ => eapply xtype_Eq'
    | sRefl _ _ => eapply xtype_Refl'
    | sAx _ => eapply type_Ax ; [| lazy ; try reflexivity ]
    | _ => fail "No introduction rule for" t
    end
  | _ => fail "Not applicable"
  end.

Ltac ettcheck1 :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-x ?t : ?T =>
    first [
      eapply meta_conv ; [ ettintro | lazy ; reflexivity ]
    | eapply type_conv ; [ ettintro | .. ]
    (* | eapply meta_ctx_conv ; [ *)
    (*     eapply meta_conv ; [ ettintro | lazy ; try reflexivity ] *)
    (*   | cbn ; try reflexivity *)
    (*   ] *)
    ]
  | |- wf ?Σ ?Γ => first [ assumption | eapply xwf_snoc' | econstructor ]
  | |- sSort _ = sSort _ => first [ lazy ; reflexivity | shelve ]
  | |- type_glob _ => first [ assumption | glob ]
  | |- xtype_glob _ => first [ assumption | xglob ]
  | _ => fail "Not applicable"
  end.

Ltac ettcheck' := ettcheck1 ; try (lazy ; omega).

Ltac ettcheck := repeat ettcheck'.