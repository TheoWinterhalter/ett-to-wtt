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

Definition rev_mapi (k : nat) {A B} (f : nat -> A -> B) (l : list A) : list B :=
  let fix aux (i : nat) (l : list A) (acc : list B) : list B :=
    match l with
    | [] => acc
    | x :: l => aux (S i) l (f i x :: acc)
    end
  in aux k l [].

Lemma rev_mapi_cons :
  forall {A B} {f : nat -> A -> B} {k a l},
    rev_mapi k f (a :: l) = rev_mapi (S k) f l ++ [ f k a ].
Proof.
  intros A B f.
  unfold rev_mapi.
  match goal with
  | |- forall k a l, ?faux _ _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc i, aux i l acc = aux i l [] ++ acc).
  { intro l. induction l ; intros acc i.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [f i a]). rewrite IHl.
      change (f i a :: acc) with ([f i a] ++ acc)%list.
      auto with datatypes.
  }
  intros k l a.
  apply h.
Defined.

Lemma app_cons_app :
  forall {A} {l1 : list A} {a l2},
    l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  intros A l1. induction l1 as [| b l1 ih ].
  - reflexivity.
  - intros a l2. cbn. rewrite ih. reflexivity.
Defined.

Lemma extendi_comp :
  forall {i Σ name l},
    extendi i Σ name l =
    rev_mapi i (fun i => decl (name @ string_of_nat i)) l ++ Σ.
Proof.
  intros i Σ name l. revert i Σ.
  induction l as [| A l ih ] ; intros i Σ.
  - reflexivity.
  - rewrite extendi_cons. rewrite ih. rewrite rev_mapi_cons.
    apply app_cons_app.
Defined.

Notation extend := (extendi 0).

Open Scope nat_scope.

Inductive allfresh : sglobal_context -> Type :=
| allfresh_nil : allfresh []
| allfresh_cons Σ d : allfresh Σ -> fresh_glob d.(dname) Σ -> allfresh (d :: Σ).

Derive Signature for allfresh.

Lemma lookup_skip :
  forall {Σ na A l},
    let d := decl na A in
    let Σ' := l ++ d :: Σ in
    allfresh Σ' ->
    lookup_glob Σ' na = Some A.
Proof.
  intros Σ na A l d Σ' hf.
  revert Σ na A d Σ' hf. induction l as [| B l ih ].
  - intros Σ na A d Σ' hf. cbn.
    destruct (ident_eq_spec na na).
    + reflexivity.
    + exfalso. auto.
  - intros Σ na A d Σ' hf. cbn.
    subst Σ'. cbn in hf. dependent destruction hf.
    specialize (ih _ _ _ hf). rewrite ih.
    erewrite ident_neq_fresh ; try eassumption.
    reflexivity.
Defined.

Lemma lookup_extendi :
  forall {Σ name ob i j},
    let Σ' := extendi i Σ name ob in
    allfresh Σ' ->
    j < #|ob| ->
    lookup_glob Σ' (name @ string_of_nat (i + j)) = nth_error ob j.
Proof.
  intros Σ name ob i j Σ' hf hj.
  revert Σ i j Σ' hf hj. induction ob as [| A ob ih ].
  - intros Σ i j Σ' hf hj. cbn in *. inversion hj.
  - intros Σ i j Σ' hf hj. cbn. destruct j.
    + subst Σ'. rewrite extendi_comp.
      rewrite extendi_comp in hf. rewrite rev_mapi_cons in hf.
      replace (i + 0) with i by myomega.
      match goal with
      | |- lookup_glob (?ob ++ ?d' :: _) ?na' = _ =>
        set (l := ob) in * ;
        set (d := d') in * ;
        set (na := na') in *
      end.
      clear - hf. rewrite <- app_cons_app in hf. cbn.
      eapply lookup_skip. assumption.
    + cbn. replace (i + S j) with (S i + j) by myomega.
      eapply ih.
      * assumption.
      * cbn in hj. myomega.
Defined.

Lemma lookup_extend :
  forall {Σ name A obb obe},
    let Σ' := extend Σ name (obb ++ (A :: obe)) in
    allfresh Σ' ->
    lookup_glob Σ' (name @ string_of_nat #|obb|) = Some A.
Proof.
  intros Σ name A obb obe Σ' hf.
  Opaque length.
  erewrite (lookup_extendi (i := 0)).
  Transparent length.
  - rewrite nth_error_app2 by reflexivity.
    replace (#|obb| - #|obb|) with 0 by myomega.
    reflexivity.
  - assumption.
  - rewrite app_length. cbn. myomega.
Defined.

Lemma xtype_glob_allfresh :
  forall {Σ},
    xtype_glob Σ ->
    allfresh Σ.
Proof.
  intros Σ h. induction h.
  - constructor.
  - constructor.
    + assumption.
    + assumption.
Defined.

Lemma fresh_glob_skip :
  forall {id Σ Ξ},
    fresh_glob id (Ξ ++ Σ) ->
    fresh_glob id Σ.
Proof.
  intros id Σ Ξ h. revert id Σ h.
  induction Ξ as [| d Ξ ih ] ; intros id Σ h.
  - assumption.
  - eapply ih. dependent destruction h. assumption.
Defined.

Lemma lookup_skip_eq :
  forall {Ξ Σ id A},
    lookup_glob Σ id = Some A ->
    allfresh (Ξ ++ Σ) ->
    lookup_glob (Ξ ++ Σ) id = Some A.
Proof.
  intro Ξ. induction Ξ as [| d Ξ ih ] ; intros Σ id A h hf.
  - cbn. assumption.
  - cbn. dependent destruction hf. apply fresh_glob_skip in f.
    erewrite ih ; try eassumption.
    erewrite ident_neq_fresh ; try eassumption.
    reflexivity.
Defined.

Ltac reset H :=
  let v := (eval unfold H in H) in
  subst H ; set (H := v) in *.

Ltac discharge :=
  try (intros ;
  match goal with
  | H : None = Some _ |- _ => discriminate H
  end).

Lemma _ettcheck_sound :
  forall Σ Γ t A ob name obb obe,
    _ettcheck Σ Γ t A = Some ob ->
    let Σ' := extend Σ name (obb ++ ob ++ obe) in
    xtype_glob Σ' ->
    wf Σ' Γ ->
    Σ' ;;; Γ |-x A : Ty ->
    Σ' ;;; Γ |-x t : A.
Proof with discharge.
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
           eapply type_Ax. rewrite lookup_extend.
           ++ reflexivity.
           ++ apply xtype_glob_allfresh. assumption.
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
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob2 eq2 h. inversion h. subst. clear h.
    specialize (IHt1 _ _ _ _ name obb (ob2 ++ ettconv Γ Ty A ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1) (ettconv Γ Ty A ++ obe) eq2).
    rewrite <- app_assoc in IHt2.
    revert Σ' hg hA hw. rewrite <- 2!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    reset Σ'.
    eapply type_conv.
    + eapply xtype_Prod'.
      * assumption.
      * eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * intro hw'. eapply IHt2 ; try assumption.
        eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      case_eq (eq_term Ty A).
      * intro eq. eapply eq_alpha.
        -- eapply eq_term_spec. assumption.
        -- eapply xtype_Sort'.
      * intro neq. clear IHt1 IHt2 hA hw. revert Σ' hg.
        rewrite neq. cbn.
        rewrite 2!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ (Γ,, t1) t3 t2) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2 h. inversion h. subst. clear h.
    specialize (IHt1 _ _ _ _ name (obb ++ ob1) (ob3 ++ ettconv Γ (sProd nx t1 t2) A ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) (ettconv Γ (sProd nx t1 t2) A ++ obe) eq2).
    specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ ettconv Γ (sProd nx t1 t2) A ++ obe) eq3).
    rewrite <- app_assoc in IHt1.
    rewrite <- 2!app_assoc in IHt2.
    revert Σ' hg hA hw. rewrite <- 3!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    specialize (IHt3 hg).
    reset Σ'.
    eapply type_conv.
    + eapply xtype_Lambda'.
      * assumption.
      * assumption.
      * eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * intro. eapply IHt3 ; try assumption.
        eapply IHt2 ; try assumption.
        eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      case_eq (eq_term (sProd nx t1 t2) A).
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 IHt3 hA hw. revert Σ' hg.
        rewrite neq. cbn.
        rewrite 3!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 (sProd nAnon t2 t3)) ...
    intros ob1 eq1. case_eq (_ettcheck Σ Γ t4 t2) ...
    intros ob2 eq4. case_eq (_ettcheck Σ Γ t2 Ty) ...
    intros ob3 eq2. case_eq (_ettcheck Σ (Γ,, t2) t3 Ty) ...
    intros ob4 eq3 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name obb (ob2 ++ ob3 ++ ob4 ++ obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) (ob4 ++ obeq ++ obe) eq2).
    specialize (IHt3 _ _ _ _ name (obb ++ ob1 ++ ob2 ++ ob3) (obeq ++ obe) eq3).
    specialize (IHt4 _ _ _ _ name (obb ++ ob1) (ob3 ++ ob4 ++ obeq ++ obe) eq4).
    rewrite <- 2!app_assoc in IHt2.
    rewrite <- 3!app_assoc in IHt3.
    rewrite <- app_assoc in IHt4.
    revert Σ' hg hA hw. rewrite <- 4!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    specialize (IHt3 hg).
    specialize (IHt4 hg).
    reset Σ'.
    eapply type_conv.
    + eapply xtype_App' ; try assumption.
      * eapply IHt1 ; try assumption.
        eapply xtype_Prod' ; try assumption.
        -- eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
        -- intro. eapply IHt3 ; try assumption.
           eapply xtype_Sort'.
      * eapply IHt4 ; try assumption.
        eapply IHt2 ; try assumption.
        eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 IHt3 IHt4 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 4!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob2 eq2 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name obb (ob2 ++ obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1) (obeq ++ obe) eq2).
    rewrite <- app_assoc in IHt2.
    revert Σ' hg hA hw. rewrite <- 2!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    reset Σ'.
    eapply type_conv.
    + eapply xtype_Sum' ; try assumption.
      * eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * intro. eapply IHt2 ; try assumption.
        eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 2!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t3 t1) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t4 (t2 {0 := t3})) ...
    intros ob2 eq4. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob3 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob4 eq2 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name (obb ++ ob1 ++ ob2) (ob4 ++ obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2 ++ ob3) (obeq ++ obe) eq2).
    specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ ob4 ++ obeq ++ obe) eq3).
    specialize (IHt4 _ _ _ _ name (obb ++ ob1) (ob3 ++ ob4 ++ obeq ++ obe) eq4).
    rewrite <- 2!app_assoc in IHt1.
    rewrite <- 3!app_assoc in IHt2.
    rewrite <- app_assoc in IHt4.
    revert Σ' hg hA hw. rewrite <- 4!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    specialize (IHt3 hg).
    specialize (IHt4 hg).
    reset Σ'.
    eapply type_conv.
    + eapply type_Pair ; try assumption.
      * eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eapply IHt2 ; try assumption.
        -- econstructor ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- eapply xtype_Sort'.
      * eapply IHt3 ; try assumption.
        eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eapply IHt4 ; try assumption.
        change Ty with (Ty{0 := t3}).
        eapply typing_subst ; try assumption.
        -- eapply IHt2 ; try assumption.
           ++ econstructor ; try assumption.
              eapply IHt1 ; try assumption.
              eapply xtype_Sort'.
           ++ eapply xtype_Sort'.
        -- eapply IHt3 ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 IHt3 IHt4 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 4!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t3 (sSum nAnon t1 t2)) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name (obb ++ ob1) (ob3 ++ obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) (obeq ++ obe) eq2).
    specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ obeq ++ obe) eq3).
    rewrite <- app_assoc in IHt1.
    rewrite <- 2!app_assoc in IHt2.
    revert Σ' hg hA hw. rewrite <- 3!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    specialize (IHt3 hg).
    reset Σ'.
    eapply type_conv.
    + eapply type_Pi1 ; try assumption.
      * eapply IHt3 ; try assumption.
        eapply xtype_Sum' ; try assumption.
        -- eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- intro. eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
      * eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eapply IHt2 ; try assumption.
        -- econstructor ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 IHt3 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 3!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t3 (sSum nAnon t1 t2)) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name (obb ++ ob1) (ob3 ++ obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) (obeq ++ obe) eq2).
    specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ obeq ++ obe) eq3).
    rewrite <- app_assoc in IHt1.
    rewrite <- 2!app_assoc in IHt2.
    revert Σ' hg hA hw. rewrite <- 3!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    specialize (IHt3 hg).
    reset Σ'.
    eapply type_conv.
    + eapply type_Pi2 ; try assumption.
      * eapply IHt3 ; try assumption.
        eapply xtype_Sum' ; try assumption.
        -- eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- intro. eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
      * eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eapply IHt2 ; try assumption.
        -- econstructor ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 IHt3 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 3!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t2 t1) ...
    intros ob1 eq2. case_eq (_ettcheck Σ Γ t3 t1) ...
    intros ob2 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob3 eq1 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name (obb ++ ob1 ++ ob2) (obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name obb (ob2 ++ ob3 ++ obeq ++ obe) eq2).
    specialize (IHt3 _ _ _ _ name (obb ++ ob1) (ob3 ++ obeq ++ obe) eq3).
    rewrite <- 2!app_assoc in IHt1.
    rewrite <- app_assoc in IHt3.
    revert Σ' hg hA hw. rewrite <- 3!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    specialize (IHt3 hg).
    reset Σ'.
    eapply type_conv.
    + eapply xtype_Eq' ; try assumption.
      * eapply IHt2 ; try assumption.
        eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eapply IHt3 ; try assumption.
        eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 IHt3 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 3!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t2 t1) ...
    intros ob1 eq2. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1 h. inversion h. subst. clear h.
    match goal with
    | _ := context [ ettconv ?Γ ?A ?B ] |- _ => set (obeq := ettconv Γ A B) in *
    end.
    specialize (IHt1 _ _ _ _ name (obb ++ ob1) (obeq ++ obe) eq1).
    specialize (IHt2 _ _ _ _ name obb (ob2 ++ obeq ++ obe) eq2).
    rewrite <- app_assoc in IHt1.
    revert Σ' hg hA hw. rewrite <- 2!app_assoc. intros Σ' hg hA hw.
    specialize (IHt1 hg).
    specialize (IHt2 hg).
    reset Σ'.
    eapply type_conv.
    + eapply xtype_Refl' ; try assumption.
      eapply IHt2 ; try assumption.
      eapply IHt1 ; try assumption.
      eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in *.
      match goal with
      | _ := context [ eq_term ?A ?B ] |- _ => case_eq (eq_term A B)
      end.
      * intro eq. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear IHt1 IHt2 hA hw. revert obeq Σ' hg.
        rewrite neq. cbn.
        rewrite 2!app_assoc.
        intros hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (lookup_glob Σ id) ...
    intros B eq h. inversion h. clear h.
    eapply type_conv.
    + eapply type_Ax. revert Σ' hg hw hA.
      rewrite extendi_comp. intros Σ' hg hw hA.
      match goal with
      | _ := ?x ++ _ |- _ => set (Ξ := x) in *
      end. erewrite lookup_skip_eq ; try eassumption.
      * reflexivity.
      * apply xtype_glob_allfresh. assumption.
    + eassumption.
    + unfold ettconv in *.
      case_eq (eq_term B A).
      * intro e. eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
      * intro neq. clear hA hw. revert H0 Σ' hg.
        rewrite neq. cbn.
        intros h hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. subst. rewrite lookup_extend.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
Defined.

Definition ettcheck (Σ : sglobal_context) (Γ : scontext) (t : sterm) (T : sterm)
  : option (list sterm) :=
  ob1 <- _ettcheck Σ Γ T Ty ;;
  ob2 <- _ettcheck Σ Γ t T ;;
  ret (ob1 ++ ob2).

Ltac discharge ::=
  try (
    intros ; cbn in * ;
    match goal with
    | H : None = Some _ |- _ => discriminate H
    end
  ).

Lemma ettcheck_sound :
  forall {Σ Γ t A ob name},
    ettcheck Σ Γ t A = Some ob ->
    let Σ' := extend Σ name ob in
    xtype_glob Σ' ->
    wf Σ' Γ ->
    Σ' ;;; Γ |-x t : A.
Proof with discharge.
  intros Σ Γ t A ob name eq Σ' hg hw.
  revert eq. unfold ettcheck.
  case_eq (_ettcheck Σ Γ A Ty) ... intros ob1 eq1.
  case_eq (_ettcheck Σ Γ t A) ... intros ob2 eq2.
  cbn. intro eq. inversion eq. clear eq. subst.
  revert Σ' hw hg.
  replace (ob1 ++ ob2) with (ob1 ++ ob2 ++ [])
    by (now rewrite app_nil_r).
  intros Σ' hw hg.
  eapply _ettcheck_sound ; try assumption.
  reset Σ'.
  revert Σ' hw hg.
  replace (ob1 ++ ob2 ++ []) with ([] ++ ob1 ++ ob2)
    by (now rewrite app_nil_r, app_nil_l).
  intros Σ' hw hg.
  eapply _ettcheck_sound ; try assumption.
  reset Σ'. eapply xtype_Sort'.
Defined.

Corollary ettcheck_nil_sound :
  forall {Σ t A ob name},
    ettcheck Σ [] t A = Some ob ->
    let Σ' := extend Σ name ob in
    xtype_glob Σ' ->
    Σ' ;;; [] |-x t : A.
Proof.
  intros Σ t A ob name eq Σ' hg.
  eapply ettcheck_sound ; try assumption.
  constructor.
Defined.
