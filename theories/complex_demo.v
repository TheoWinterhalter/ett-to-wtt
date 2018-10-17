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

Definition app_assoc :=
fun (A : Type) (l m n : list A) =>
list_ind (fun l0 : list A => l0 ++ m ++ n = (l0 ++ m) ++ n)
  (let H : n = n := eq_refl in
   (let H0 : m = m := eq_refl in (let H1 : A = A := eq_refl in (fun (_ : A = A) (_ : m = m) (_ : n = n) => eq_refl) H1) H0) H)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
   let H : l0 ++ m ++ n = (l0 ++ m) ++ n := IHl in
   (let H0 : a = a := eq_refl in
    (let H1 : A = A := eq_refl in
     (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
      eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ m ++ n)) eq_refl) (f_equal (cons a) H4)) H1) H0) H) l.

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
    - cbn.
      pose proof (IHl [f i a] (S i)) as e1.
      pose proof (IHl (f i a :: acc) (S i)) as e2.
      refine (eq_trans e2 _).
      change (f i a :: acc) with ([f i a] ++ acc).
      rewrite e1. apply app_assoc.
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

Ltac tryone a a' H :=
  destruct a, a'; simpl in *; try (reflexivity || discriminate).

Lemma ascii_Compare_eq : forall x y, ascii_compare x y = Eq <-> x = y.
Proof.
  destruct x as [a b c d e f g h].
  destruct y as [a' b' c' d' e' f' g' h'].
  split. intros H.
  tryone a a' H;
    tryone b b' H;
    tryone c c' H;
    tryone d d' H;
    tryone e e' H;
    tryone f f' H;
    tryone g g' H;
    tryone h h' H; reflexivity.
  intros H; injection H. intros; subst.
  destruct a', b', c', d', e', f', g', h'; reflexivity.
Defined.

Lemma ascii_compare_Lt x y : ascii_compare x y = Gt <-> ascii_compare y x = Lt.
Proof.
  destruct x as [a b c d e f g h].
  destruct y as [a' b' c' d' e' f' g' h'].
  split.
  intros H.
  tryone a a' H;
    tryone b b' H;
    tryone c c' H;
    tryone d d' H;
    tryone e e' H;
    tryone f f' H;
    tryone g g' H;
    tryone h h' H; try reflexivity.
  intros H.
  tryone a a' H;
    tryone b b' H;
    tryone c c' H;
    tryone d d' H;
    tryone e e' H;
    tryone f f' H;
    tryone g g' H;
    tryone h h' H; try reflexivity.
Defined.

Definition ascii_Compare (x y : Ascii.ascii) : OrderedType.Compare ascii_lt eq x y.
Proof.
  case_eq (ascii_compare x y).
  intros.
  - apply OrderedType.EQ.
    now apply ascii_Compare_eq.
  - intros. apply OrderedType.LT.
    destruct x as [a b c d e f g h].
    destruct y as [a' b' c' d' e' f' g' h'].
    unfold ascii_lt. apply H.
  - intros.
    apply OrderedType.GT. red. now apply ascii_compare_Lt.
Defined.

Definition proj2 {A B : Prop} (H : A /\ B) :=
  match H with
  | conj _ H1 => H1
  end.

Lemma string_compare_eq : forall x y : string, string_compare x y = Eq <-> eq x y.
Proof.
  split.
  induction x in y |- *.
  + destruct y. reflexivity.
    discriminate.
  + destruct y. discriminate.
    simpl. destruct (ascii_Compare a a0). red in a1. rewrite a1. discriminate.
    subst a0.
    pose (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
    rewrite e. intros H. specialize (IHx _ H). rewrite IHx. reflexivity.
    red in a1. apply ascii_compare_Lt in a1. rewrite a1. discriminate.
  + intros ->.
    induction y. reflexivity.
    simpl. now rewrite (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
Defined.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq.
  case_eq (string_compare x y).
  all: intro e ; constructor.
  1: apply string_compare_eq ; assumption.
  all: intro bot.
  all: apply string_compare_eq in bot.
  all: rewrite bot in e.
  all: discriminate e.
Defined.

Fact ident_neq_fresh :
  forall {Σ id ty d},
    lookup_glob Σ id = Some ty ->
    fresh_glob (dname d) Σ ->
    ident_eq id (dname d) = false.
Proof.
  intro Σ. induction Σ ; intros id ty d h hf.
  - cbn in h. discriminate h.
  - cbn in h. dependent destruction hf.
    case_eq (ident_eq id (dname d0)) ;
    intro e ; rewrite e in h.
    + inversion h as [ h' ]. subst. clear h.
      destruct (ident_eq_spec id (dname d)).
      * subst. destruct (ident_eq_spec (dname d) (dname d0)).
        -- exfalso. easy.
        -- easy.
      * reflexivity.
    + eapply IHΣ ; eassumption.
Defined.

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

Lemma nth_error_app2 A (l : list A) l' n :
  length l <= n ->
  nth_error (l++l') n = nth_error l' (n- length l).
Proof.
  revert l.
  induction n; intros [|a l] H; auto.
  - inversion H.
  - simpl in *. apply IHn. myomega.
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

Definition app_length :=
fun (A : Type) (l : list A) =>
list_ind (fun l0 : list A => forall l' : list A, #|l0 ++ l'| = #|l0| + #|l'|) (fun l' : list A => eq_refl)
  (fun (a : A) (l0 : list A) (IHl : forall l' : list A, #|l0 ++ l'| = #|l0| + #|l'|) (l' : list A) =>
   f_equal_nat nat S #|l0 ++ l'| (#|l0| + #|l'|) (IHl l')) l.

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

Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    rewrite <- IHl. reflexivity.
Defined.

Definition some_inj (A : Type) (x y : A) (H : Some x = Some y) : x = y :=
  f_equal (fun e : option A =>
             match e with
             | Some a => a
             | None => x
             end) H.

Lemma nth_error_Some_safe_nth A (l : list A) n c :
  forall e : nth_error l n = Some c, safe_nth l (exist _ n (nth_error_isdecl e)) = c.
Proof.
  intros H.
  pose proof (nth_error_safe_nth _ _ (nth_error_isdecl H)).
  pose proof (eq_trans (eq_sym H) H0).
  apply some_inj in H1. exact (eq_sym H1).
Defined.

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
      * intros _ h. apply some_inj in h. subst. cbn in Σ'.
        eapply type_conv.
        -- eapply type_Rel.
        -- eassumption.
        -- erewrite nth_error_Some_safe_nth with (e := eq).
           eapply reflection. eapply close_goal ; try eassumption.
           eapply type_Ax. eapply lookup_extend.
           apply xtype_glob_allfresh. assumption.
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
      * intros _ h. apply some_inj in h. subst. cbn in Σ'.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob2 eq2 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ (Γ,, t1) t3 t2) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 (sProd nAnon t2 t3)) ...
    intros ob1 eq1. case_eq (_ettcheck Σ Γ t4 t2) ...
    intros ob2 eq4. case_eq (_ettcheck Σ Γ t2 Ty) ...
    intros ob3 eq2. case_eq (_ettcheck Σ (Γ,, t2) t3 Ty) ...
    intros ob4 eq3 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob2 eq2 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t3 t1) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t4 (t2 {0 := t3})) ...
    intros ob2 eq4. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob3 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob4 eq2 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t3 (sSum nAnon t1 t2)) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t3 (sSum nAnon t1 t2)) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t2 t1) ...
    intros ob1 eq2. case_eq (_ettcheck Σ Γ t3 t1) ...
    intros ob2 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob3 eq1 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t2 t1) ...
    intros ob1 eq2. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1 h. apply some_inj in h. subst.
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
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (lookup_glob Σ id) ...
    intros B eq h. apply some_inj in h.
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
      * intro neq. clear hA hw. revert h Σ' hg.
        rewrite neq. cbn.
        intros h hg.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. subst. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
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

Definition app_nil_r :=
fun (A : Type) (l : list A) =>
list_ind (fun l0 : list A => l0 ++ [] = l0) (let H : A = A := eq_refl in (fun _ : A = A => eq_refl) H)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ [] = l0) =>
   let H : l0 ++ [] = l0 := IHl in
   (let H0 : a = a := eq_refl in
    (let H1 : A = A := eq_refl in
     (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ [] = l0) =>
      eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ [])) eq_refl) (f_equal (cons a) H4)) H1) H0) H) l.

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
    by (refine (eq_trans _ (app_nil_r _ (ob1 ++ ob2))) ; apply app_assoc).
  intros Σ' hw hg.
  eapply _ettcheck_sound ; try assumption.
  reset Σ'.
  revert Σ' hw hg.
  replace (ob1 ++ ob2 ++ []) with ([] ++ ob1 ++ ob2)
    by (refine (eq_sym _) ; refine (eq_trans _ (app_nil_r _ (ob1 ++ ob2))) ; apply app_assoc).
  intros Σ' hw hg.
  eapply _ettcheck_sound ; try assumption.
  reset Σ'. eapply xtype_Sort'.
Defined.

Corollary ettcheck_nil_sound :
  forall {Σ t A ob} name,
    ettcheck Σ [] t A = Some ob ->
    let Σ' := extend Σ name ob in
    xtype_glob Σ' ->
    Σ' ;;; [] |-x t : A.
Proof.
  intros Σ t A ob name eq Σ' hg.
  eapply ettcheck_sound ; try assumption.
  constructor.
Defined.

(* Global context should be typable in ITT and as such
   we only check it ETT under no obligations.
 *)
Fixpoint ettcheck_ctx Σ :=
  match Σ with
  | d :: Σ =>
    match ettcheck Σ [] (dtype d) Ty with
    | Some [] => ettcheck_ctx Σ
    | _ => false
    end
  | [] => true
  end.

Ltac discharge ::=
  try (intros ; discriminate).

Lemma ettcheck_ctx_sound :
  forall {Σ},
    ettcheck_ctx Σ = true ->
    allfresh Σ ->
    xtype_glob Σ.
Proof with discharge.
  intro Σ. induction Σ as [| d Σ ih ] ; intros eq hf.
  - constructor.
  - dependent destruction hf.
    rename Σ0 into Σ, d0 into d.
    revert eq. unfold ettcheck_ctx.
    case_eq (ettcheck Σ [] (dtype d) Ty) ... intros ob eq.
    destruct ob ... intro h.
    econstructor.
    + eapply ih ; assumption.
    + assumption.
    + change Σ with (extend Σ "foo" []).
      eapply ettcheck_nil_sound.
      * assumption.
      * cbn. eapply ih ; assumption.
Defined.

Fixpoint isxcomp t :=
  match t with
  | sRel n => true
  | sSort s => true
  | sProd _ A B => isxcomp A && isxcomp B
  | sLambda _ A B t => isxcomp A && isxcomp B && isxcomp t
  | sApp u A B v => isxcomp A && isxcomp B && isxcomp u && isxcomp v
  | sSum _ A B => isxcomp A && isxcomp B
  | sPair A B u v => isxcomp A && isxcomp B && isxcomp u && isxcomp v
  | sPi1 A B p => isxcomp A && isxcomp B && isxcomp p
  | sPi2 A B p => isxcomp A && isxcomp B && isxcomp p
  | sEq A u v => isxcomp A && isxcomp u && isxcomp v
  | sRefl A u => isxcomp A && isxcomp u
  | sAx _ => true
  | _ => false
  end.

Lemma isxcomp_sound :
  forall {t},
    isxcomp t = true ->
    Xcomp t.
Proof.
  intro t. induction t ; intro eq.
  all: try discriminate eq.
  all: try solve [constructor].
  all: cbn in eq ; repeat destruct_andb ; econstructor ; easy.
Defined.

Fixpoint ittcheck_ctx fuel Σ :=
  match Σ with
  | d :: Σ =>
    isxcomp (dtype d) && ittcheck fuel Σ [] (dtype d) Ty && ittcheck_ctx fuel Σ
  | [] => true
  end.

Lemma ittcheck_ctx_sound :
  forall {fuel Σ},
    ittcheck_ctx fuel Σ = true ->
    allfresh Σ ->
    type_glob Σ.
Proof with discharge.
  intros fuel Σ. induction Σ as [| d Σ ih ] ; intros eq hf.
  - constructor.
  - dependent destruction hf.
    rename Σ0 into Σ, d0 into d.
    revert eq. unfold ittcheck_ctx.
    case_eq (isxcomp (dtype d)) ... intro e. cbn.
    case_eq (ittcheck fuel Σ [] (dtype d) Ty) ... cbn.
    intros eq h.
    econstructor.
    + eapply ih ; assumption.
    + assumption.
    + eexists. eapply ittcheck_sound.
      * eassumption.
      * eapply ih ; assumption.
      * constructor.
    + eapply isxcomp_sound. assumption.
Defined.

Fixpoint isfresh id Σ :=
  match Σ with
  | d :: Σ => negb (ident_eq (dname d) id) && isfresh id Σ
  | [] => true
  end.

Lemma isfresh_sound :
  forall {id Σ},
    isfresh id Σ = true ->
    fresh_glob id Σ.
Proof.
  intros id Σ. induction Σ as [| d Σ ih ] ; intro h.
  - constructor.
  - cbn in h. destruct_andb.
    econstructor.
    + eapply ih. assumption.
    + destruct (ident_eq_spec (dname d) id).
      * cbn in *. discriminate.
      * assumption.
Defined.

Fixpoint isallfresh Σ :=
  match Σ with
  | d :: Σ => isfresh (dname d) Σ && isallfresh Σ
  | [] => true
  end.

Lemma isallfresh_sound :
  forall {Σ},
    isallfresh Σ = true ->
    allfresh Σ.
Proof.
  intro Σ. induction Σ as [| d Σ ih ] ; intro h.
  - constructor.
  - cbn in h. destruct_andb.
    econstructor.
    + eapply ih. assumption.
    + eapply isfresh_sound. assumption.
Defined.

(* We now attempt a complete translation procedure *)

(* Not Tail-recursive for the tile being *)
(* TODO Use monap_map? *)
Fixpoint map_tsl l : TemplateMonad (list term) :=
  match l with
  | t :: l =>
    match tsl_rec (2 ^ 18) Σ [] t axoc with
    | FinalTranslation.Success _ t =>
      l <- map_tsl l ;;
      ret (t :: l)
    | _ => tmFail "Cannot refine obligation into a Coq term"
    end
  | [] => ret []
  end.

(* Ask the user to prove obligations and returns the corresponding association table *)
Fixpoint map_lemma (name : ident) (l : list term) : TemplateMonad (assoc term) :=
  match l with
  | t :: l =>
    ty <- tmUnquoteTyped Type t ;;
    name <- tmFreshName name ;;
    lem <- tmLemma name (ty : Type) ;;
    tlem <- tmQuote lem ;;
    axoc <- map_lemma name l ;;
    ret ((name --> tlem) axoc)
  | [] => ret [< >]
  end.

Fact istrans_nil {Σ} :
  ctxtrans Σ nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition type_translation {Σ} hg {Γ t A} h {Γ'} hΓ :=
  fst (@complete_translation _ Σ hg) Γ t A h Γ' hΓ.

Definition Translate ident : TemplateMonad () :=
  (* First we quote the term to its TC representation *)
  (* TODO We should get the TC global context as well! *)
  entry <- tmQuoteConstant ident false ;;
  match entry with
  | DefinitionEntry {| definition_entry_body := tm ; definition_entry_type := ty |} =>
    (* We get its type and body and elaborate them to ETT terms *)
    (* TODO We should get the correspondence between axioms and Coq constants
       somehow.
     *)
    pretm <- tmEval lazy (fullquote (2 ^ 18) Σ [] tm indt constt cot) ;;
    prety <- tmEval lazy (fullquote (2 ^ 18) Σ [] ty indt constt cot) ;;
    match pretm, prety with
    | Success tm, Success ty =>
      (* We pick the name framework of obligations *)
      obname <- tmEval all (ident @ "_obligation_") ;;
      name <- tmEval all (obname @ "0") ;;
      (* We then typecheck the term in ETT *)
      (* TODO We need a sglobal_context *)
      let ch := ettcheck [] [] tm ty in
      match ch as o
      return (ch = o -> TemplateMonad ())
      with
      | Some obl => fun (eq : ch = Some obl) =>
        (* obl <- tmEval all obl ;; *)
        (* We now have the list of obligations *)
        (* TODO Check the extended global context is well formed (at least in ITT) *)
        (* We push them into TC *)
        tc_obl <- map_tsl obl ;;
        tc_obl <- tmEval lazy tc_obl ;;
        (* tmPrint tc_obl ;; *)
        (* TODO We then turn them into a list of definitions *)
        (* We ask the user to prove the obligations in Coq *)
        axoc <- map_lemma name tc_obl ;;
        (* Once they are proven we can safely apply soundness to get an ETT
           derivation, but first we need to check the whole global context *)
        (* Σ' <- tmEval lazy (extend [] obname obl) ;; *)
        let Σ' := extend [] obname obl in
        (* First we check freshness of Σ' *)
        match isallfresh Σ' as b
        return (isallfresh Σ' = b -> TemplateMonad ())
        with
        | true => fun eqf =>
          (* Then we check Σ' in ETT *)
          match ettcheck_ctx Σ' as b
          return (ettcheck_ctx Σ' = b -> TemplateMonad ())
          with
          | true => fun eqcx =>
            (* We now have a derivation of our term in ETT *)
            let hf := isallfresh_sound eqf in
            let xhg := ettcheck_ctx_sound eqcx hf in
            let der := ettcheck_nil_sound obname eq xhg in
            (* der' <- tmEval all der ;; *)
            (* tmPrint der' ;; *)
            (* Next we check the global context makes sense in ITT *)
            match ittcheck_ctx (2 ^ 18) Σ' as b
            return (ittcheck_ctx (2 ^ 18) Σ' = b -> TemplateMonad ())
            with
            | true => fun eqc =>
              let hg := ittcheck_ctx_sound eqc hf in
              let '(_ ; itt_tm ; _) := type_translation hg der istrans_nil in
              t <- tmEval lazy (tsl_rec (2 ^ 18) Σ [] itt_tm axoc) ;;
              match t with
              | FinalTranslation.Success _ t =>
                tname <- tmEval all (ident @ "ᵗ") ;;
                tmMkDefinition tname t ;;
                msg <- tmEval all ("Successfully generated " @ tname) ;;
                tmPrint msg
              | FinalTranslation.Error _ e =>
                msg <- tmEval all ("Cannot translate from ITT to TemplateCoq: " @
                  match e with
                  | FinalTranslation.NotEnoughFuel => "Not enough fuel"
                  | FinalTranslation.TranslationNotFound id => "Not found " @ id
                  | FinalTranslation.TranslationNotHandled => "Translation not handled"
                  | FinalTranslation.TypingError msg _ => "Typing error - " @ msg
                  | FinalTranslation.UnexpectedTranslation s _ _ _ => "Unexpected translation " @ s
                  end) ;;
                tmFail msg
              end
              (* tmPrint "ok" *)
            | false => fun _ => tmFail "Generated global context doesn't typecheck in ITT"
            end eq_refl
          | false => fun _ => tmFail "Generated global context doesn't typecheck in ETT"
          end eq_refl
        | false => fun _ => tmFail "Generated global context has naming conflicts"
        end eq_refl
      | None => fun (_ : ch = None) => tmFail "ETT typechecking failed"
      end eq_refl
    | _,_ => tmFail "Cannot elaborate Coq term to an ETT term"
    end
  | _ => tmFail "Expected definition of a Coq constant"
  end.

(* Not ok *)
(* Definition test (A B C : Type) (f : A -> B) (e : B = C) (u : B = A) (x : B) : C := *)
(*   {! f {! x !} !}. *)

(* Not ok *)
(* Definition test (A B : Type) (f : A -> B) (u : B = A) (x : B) : A := *)
(*   {! f {! x !} !}. *)

(* Not ok *)
Definition test (A B : Type) (f : A -> B) (u : B = A) (x : A) : A :=
  {! f x !}.

(* Ok *)
(* Definition test (A B : Type) (f : A -> B) (x : A) : B := f x. *)

(* Ok *)
(* Definition test (A B : Type) (f : A -> B) (u : B = A) (x : B) : B := *)
(*   f {! x !}. *)

(* Run TemplateProgram (Translate "test"). *)
(* Print testᵗ. *)

Definition bar := Type.

Run TemplateProgram (Translate "bar").
Print barᵗ.

Definition foo (A : Type) (x : A) := x.

Run TemplateProgram (Translate "foo").
Print fooᵗ.

Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}.

Run TemplateProgram (Translate "pseudoid").
Print pseudoidᵗ.


Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

(* For now the sglobal_context is empty so it cannot typecheck *)
(* Run TemplateProgram (Translate "vrev"). *)