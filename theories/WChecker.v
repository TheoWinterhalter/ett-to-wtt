(*! Type checker for WTT *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith Utf8.
From Equations Require Import Equations.
From Translation
Require Import util monad_utils Sorts WAst WLiftSubst WTyping WEquality WLemmata.

Section Checking.

Context `{Sort_notion : Sorts.notion}.

Inductive i_error :=
  | NotEqTerms (u v : wterm) | Msg (s : string).

Definition i_result := result i_error.

Definition getsort (T : wterm) : i_result sort :=
  match T with
  | wSort s => ret s
  | _ => raise (Msg "get_sort")
  end.

Definition getprod (T : wterm) : i_result (wterm * wterm) :=
  match T with
  | wProd A B => ret (A,B)
  | _ => raise (Msg "getprod")
  end.

Definition getsum (T : wterm) : i_result (wterm * wterm) :=
  match T with
  | wSum A B => ret (A,B)
  | _ => raise (Msg "getsum")
  end.

Definition geteq (T : wterm) : i_result (wterm * wterm * wterm) :=
  match T with
  | wEq A u v => ret (A,u,v)
  | _ => raise (Msg "geteq")
  end.

Definition gettransport (t : wterm) : i_result (wterm * wterm * wterm * wterm) :=
  match t with
  | wTransport A B e t => ret (A,B,e,t)
  | _ => raise (Msg "gettransport")
  end.

Definition assert_eq (u v : wterm) : i_result unit :=
  if eq_term u v then ret tt else raise (NotEqTerms u v).

Definition assert_eq_sort (s1 s2 : sort) : i_result unit :=
  if Sorts.eq_dec s1 s2 then ret tt else raise (Msg "assert_eq_sort").

Fixpoint wttinfer (Σ : wglobal_context) (Γ : wcontext) (t : wterm)
  : i_result wterm :=
  match t with
  | wRel n =>
     match nth_error Γ n with
     | Some A => ret (lift0 (S n) A)
     | None => raise (Msg "unboud rel")
     end
  | wSort s =>
    ret (wSort (succ s))
  | wProd A B =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    s2 <- getsort =<< wttinfer Σ (Γ ,, A) B ;;
    ret (wSort (prod_sort s1 s2))
  | wLambda A t =>
    getsort =<< wttinfer Σ Γ A ;;
    B <- wttinfer Σ (Γ ,, A) t ;;
    ret (wProd A B)
  | wApp u v =>
    Π <- getprod =<< wttinfer Σ Γ u ;;
    let '(A,B) := Π in
    assert_eq A =<< wttinfer Σ Γ v ;;
    ret (B{ 0 := v })
  | wSum A B =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    s2 <- getsort =<< wttinfer Σ (Γ ,, A) B ;;
    ret (wSort (sum_sort s1 s2))
  | wPair A B u v =>
    getsort =<< wttinfer Σ Γ A ;;
    getsort =<< wttinfer Σ (Γ,, A) B ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    assert_eq (B{ 0 := u }) =<< wttinfer Σ Γ v ;;
    ret (wSum A B)
  | wPi1 A B p =>
    assert_eq (wSum A B) =<< wttinfer Σ Γ p ;;
    getsort =<< wttinfer Σ Γ A ;;
    getsort =<< wttinfer Σ (Γ,, A) B ;;
    ret A
  | wPi2 A B p =>
    assert_eq (wSum A B) =<< wttinfer Σ Γ p ;;
    getsort =<< wttinfer Σ Γ A ;;
    getsort =<< wttinfer Σ (Γ,, A) B ;;
    ret (B{ 0 := wPi1 A B p })
  | wEq A u v =>
    s <- getsort =<< wttinfer Σ Γ A ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    assert_eq A =<< wttinfer Σ Γ v ;;
    ret (wSort (eq_sort s))
  | wRefl A u =>
    getsort =<< wttinfer Σ Γ A ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    ret (wEq A u u)
  | wJ A u P w v p =>
    getsort =<< wttinfer Σ Γ A ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    assert_eq A =<< wttinfer Σ Γ v ;;
    getsort =<< wttinfer Σ (Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0))) P ;;
    assert_eq (wEq A u v) =<< wttinfer Σ Γ p ;;
    assert_eq (P{ 1 := u }{ 0 := wRefl A u }) =<< wttinfer Σ Γ w ;;
    ret (P{ 1 := v }{ 0 := p })
  | wTransport A B p t =>
    s <- getsort =<< wttinfer Σ Γ A ;;
    assert_eq_sort s =<< getsort =<< wttinfer Σ Γ B ;;
    assert_eq (wEq (wSort s) A B) =<< wttinfer Σ Γ p ;;
    assert_eq A =<< wttinfer Σ Γ t ;;
    ret B
  | wBeta t u =>
    A <- wttinfer Σ Γ u ;;
    B <- wttinfer Σ (Γ,, A) t ;;
    ret (wEq (B{ 0 := u }) (wApp (wLambda A t) u) (t{ 0 := u }))
  | wK A u p =>
    getsort =<< wttinfer Σ Γ A ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    assert_eq (wEq A u u) =<< wttinfer Σ Γ p ;;
    ret (wEq (wEq A u u) p (wRefl A u))
  | wFunext f g p =>
    Π <- getprod =<< wttinfer Σ Γ f ;;
    let '(A,B) := Π in
    assert_eq (wProd A B) =<< wttinfer Σ Γ g ;;
    assert_eq (wProd A
                 (wEq B (wApp (lift0 1 f) (wRel 0))
                        (wApp (lift0 1 g) (wRel 0))))
              =<< wttinfer Σ Γ p ;;
    ret (wEq (wProd A B) f g)
  | wJBeta u P w =>
    A <- wttinfer Σ Γ u ;;
    getsort =<< wttinfer Σ (Γ,, A,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0))) P ;;
    assert_eq (P{ 1 := u }{ 0 := wRefl A u }) =<< wttinfer Σ Γ w ;;
    ret (wEq (P{ 1 := u }{ 0 := wRefl A u })
             (wJ A u P w u (wRefl A u))
             w)
  | wTransportBeta A t =>
    s <- getsort =<< wttinfer Σ Γ A ;;
    assert_eq A =<< wttinfer Σ Γ t ;;
    ret (wEq A (wTransport A A (wRefl (wSort s) A) t) t)
  | wPairEta p =>
    T <- getsum =<< wttinfer Σ Γ p ;;
    let '(A,B) := T in
    ret (wEq (wSum A B) (wPair A B (wPi1 A B p) (wPi2 A B p)) p)
  | wProdExt A p =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    E <- geteq =<< wttinfer Σ (Γ,, A) p ;;
    let '(S2,B1,B2) := E in
    s2 <- getsort S2 ;;
    ret (wEq (wSort (prod_sort s1 s2)) (wProd A B1) (wProd A B2))
  | wSumExt A p =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    E <- geteq =<< wttinfer Σ (Γ,, A) p ;;
    let '(S2,B1,B2) := E in
    s2 <- getsort S2 ;;
    ret (wEq (wSort (sum_sort s1 s2)) (wSum A B1) (wSum A B2))
  | wConst id =>
    match lookup_glob Σ id with
    | Some d => ret (dtype d)
    | None  => raise (Msg ("unknown constant: " ++ id))
    end
  | wDelta id =>
    match lookup_glob Σ id with
    | Some d =>
      match dbody d with
      | Some t => ret (wEq (dtype d) (wConst id) t)
      | None => raise (Msg ("not a definition: " ++ id))
      end
    | None  => raise (Msg ("unknown constant: " ++ id))
    end
  end.

Lemma type_Beta' :
  forall {Σ Γ A B t u},
    type_glob Σ ->
    Σ ;;; Γ,, A |-w t : B ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wBeta t u
             : wEq (B {0 := u}) (wApp (wLambda A t) u) (t {0 := u}).
Proof.
  intros Σ Γ A B t u hg ht hu.
  destruct (istype_type hg hu).
  econstructor ; eassumption.
Defined.

Ltac deal_assert_eq :=
  match goal with
  | h : assert_eq ?t ?u = _ |- _ =>
    unfold assert_eq in h ;
    revert h ;
    case_eq (eq_term t u) ; try (intros ? h ; discriminate h) ;
    intros
  end.

Ltac deal_getsort :=
  match goal with
  | h : getsort ?t = _ |- _ =>
    destruct t ; simpl in h ; try discriminate h ;
    inversion h ; subst ; clear h
  end.

Ltac deal_getprod :=
  match goal with
  | h : getprod ?t = _ |- _ =>
    destruct t ; simpl in h ; try discriminate h ;
    inversion h ; subst ; clear h
  end.

Ltac deal_getsum :=
  match goal with
  | h : getsum ?t = _ |- _ =>
    destruct t ; simpl in h ; try discriminate h ;
    inversion h ; subst ; clear h
  end.

Ltac deal_geteq :=
  match goal with
  | h : geteq ?t = _ |- _ =>
    destruct t ; simpl in h ; try discriminate h ;
    inversion h ; subst ; clear h
  end.

Ltac deal_gettransport :=
  match goal with
  | h : gettransport ?t = _ |- _ =>
    destruct t ; simpl in h ; try discriminate h ;
    inversion h ; subst ; clear h
  end.

Ltac deal_assert_eq_sort :=
  match goal with
  | h : assert_eq_sort ?s ?z = _ |- _ =>
    unfold assert_eq_sort in h ;
    revert h ;
    destruct (eq_dec s z) ;
    try (intros ; discriminate h) ;
    intros ; subst ; clear h
  end.

Ltac remove1 :=
  lazymatch goal with
  | |- context [ match ?t with _ => _ end ] =>
    case_eq t ; try solve [ intros ; discriminate ]
  | h : context [ match ?t with _ => _ end ] |- _ =>
    revert h ;
    case_eq t ; try solve [ intros ; discriminate ]
  end.

Ltac go eq :=
  simpl in eq ; revert eq ;
  repeat remove1 ;
  intros ;
  repeat remove1 ;
  intros ;
  inversion eq ; subst ; clear eq ;
  repeat deal_assert_eq ;
  repeat deal_geteq ;
  repeat deal_getsort ;
  repeat deal_gettransport ;
  repeat deal_getprod ;
  repeat deal_getsum ;
  repeat deal_assert_eq_sort.

Ltac one_ih :=
  lazymatch goal with
  | h : _ -> _ -> _ -> _ -> _ ;;; _ |-w ?t : _ |- _ ;;; _ |-w ?t : _ =>
    eapply h
  end.

Ltac ih :=
  one_ih ;
  first [
    eassumption
  | econstructor ; try eassumption ;
    one_ih ; eassumption
  ].

Ltac rih :=
  eapply meta_conv ; [
    ih ; eassumption
  | symmetry ; eapply eq_term_spec ; assumption
  ].

Lemma wttinfer_sound :
  forall Σ Γ t A,
    wttinfer Σ Γ t = Success A ->
    type_glob Σ ->
    wf Σ Γ ->
    Σ ;;; Γ |-w t : A.
Proof.
  intros Σ Γ t A eq hg hw.
  revert Γ A eq hw.
  induction t ; intros Γ A eq hw.
  all: try solve [ go eq ; econstructor ; try eassumption ; try ih ; try rih ].
  - go eq. econstructor ; try ih ; try rih.
    one_ih.
    + eassumption.
    + econstructor.
      * econstructor ; try eassumption. ih.
      * econstructor.
        -- match goal with
           | |- _ ;;; _ |-w lift ?n ?k _ : ?S =>
             change S with (lift n k S)
           end.
           eapply typing_lift01 ; try eassumption ; ih.
        -- eapply typing_lift01 ; try eassumption ; try rih. ih.
        -- eapply meta_conv.
           ++ econstructor.
              ** econstructor ; try eassumption. ih.
              ** cbn. reflexivity.
           ++ reflexivity.
  - go eq.
    assert (Σ ;;; Γ |-w t2 : w) as hh by ih.
    destruct (istype_type hg hh).
    eapply type_Beta' ; try eassumption ; try ih ; try rih.
  - go eq.
    assert (Σ ;;; Γ |-w t1 : w0) as hh by ih.
    destruct (istype_type hg hh).
    econstructor ; try eassumption ; try ih ; try rih.
    eapply IHt2 ; try eassumption.
    repeat eapply wf_snoc ; try eassumption.
    econstructor.
    + match goal with
      | |- _ ;;; _ |-w lift ?n ?k _ : ?S =>
        change S with (lift n k S)
      end.
      eapply typing_lift01 ; try eassumption ; ih.
    + eapply typing_lift01 ; try eassumption ; rih.
    + eapply meta_conv.
      * econstructor.
        -- econstructor ; eassumption.
        -- cbn. reflexivity.
      * reflexivity.
  Unshelve.
  all: try solve [ constructor ].
Defined.

Ltac inv_eq :=
  match goal with
  | h : wSort _ = ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  | h : wProd _ _ = ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  | h : wSum _ _ = ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  | h : wEq _ _ _ = ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  end.

Lemma assert_eq_sort_refl :
  forall {s}, assert_eq_sort s s = Success tt.
Proof.
  intro s. unfold assert_eq_sort.
  destruct (eq_dec s s).
  - reflexivity.
  - exfalso. apply n. reflexivity.
Defined.

Ltac rewih :=
  match goal with
  | [ h : exists _, _ |- _ ] =>
    let e := fresh "e" in
    destruct h as [? [e ?]] ;
    rewrite ?e
  end.

Ltac co :=
  simpl ;
  repeat rewih ;
  subst ;
  repeat inv_eq ;
  simpl ;
  unfold assert_eq ;
  rewrite ?assert_eq_sort_refl ;
  repeat (erewrite (proj2 eq_term_spec) ; [| reflexivity]) ;
  simpl ;
  eexists ; split ; [
    reflexivity
  | repeat f_equal
  ].

Lemma wttinfer_complete :
  forall {Σ Γ t A},
    Σ ;;; Γ |-w t : A ->
    exists B, wttinfer Σ Γ t = Success B /\ A = B.
Proof.
  intros Σ Γ t A h.
  induction h.
  all: try solve [ co ].
  - cbn. rewrite H0. eexists. intuition eauto.
  - simpl.
    repeat rewih. subst. simpl.
    unfold assert_eq.
    rewrite ?assert_eq_sort_refl.
    repeat (erewrite (proj2 eq_term_spec) ; [| reflexivity]).
    simpl.
    eexists. split.
    + reflexivity.
    + reflexivity.
  - simpl.
    repeat rewih. subst. simpl.
    unfold assert_eq.
    rewrite ?assert_eq_sort_refl.
    repeat (erewrite (proj2 eq_term_spec) ; [| reflexivity]).
    simpl.
    eexists. intuition reflexivity.
  - simpl. repeat rewih. subst.
    rewrite e0.
    eexists. intuition reflexivity.
  - simpl. repeat rewih. subst.
    rewrite e1. simpl.
    unfold assert_eq.
    rewrite ?assert_eq_sort_refl.
    repeat (erewrite (proj2 eq_term_spec) ; [| reflexivity]).
    simpl.
    eexists. intuition reflexivity.
  - exists (dtype d). split.
    + unfold wttinfer. rewrite_assumption. reflexivity.
    + reflexivity.
  - exists (wEq (dtype d) (wConst id) t).
    split.
    + unfold wttinfer. rewrite_assumption. rewrite_assumption. reflexivity.
    + reflexivity.
Defined.

End Checking.

Section PolymorphicSorts.

(* Polymorhpic sorts *)
Inductive psort :=
| pvar (n : nat)
| psucc (s : psort)
| pprod_sort (s1 s2 : psort)
| psum_sort (s1 s2 : psort)
| peq_sort (s : psort)
| pheq_sort (s : psort)
| ppack_sort (s : psort)
.

#[refine] Instance psort_notion : Sorts.notion := {|
  sort := psort ;
  succ := psucc ;
  prod_sort := pprod_sort ;
  sum_sort := psum_sort ;
  heq_sort := pheq_sort ;
  pack_sort := ppack_sort ;
  eq_sort := peq_sort
|}.
Proof.
  - intros s z. decide equality.
    decide equality.
  - intros s z e.
    destruct s, z ; inversion e ; eauto.
Defined.

Fixpoint instantiate_sort `{ S : Sorts.notion }
           (inst : nat -> @sort S) (s : @sort psort_notion)
  : @sort S :=
  match s with
  | pvar n => inst n
  | psucc s => succ (instantiate_sort inst s)
  | pprod_sort s1 s2 =>
    prod_sort (instantiate_sort inst s1) (instantiate_sort inst s2)
  | psum_sort s1 s2 =>
    sum_sort (instantiate_sort inst s1) (instantiate_sort inst s2)
  | peq_sort s => eq_sort (instantiate_sort inst s)
  | pheq_sort s => heq_sort (instantiate_sort inst s)
  | ppack_sort s => pack_sort (instantiate_sort inst s)
  end.

Definition instantiate_sorts `{ S : Sorts.notion }
           (inst : nat -> @sort S)
  : @wterm psort_notion -> @wterm S :=
  fix f (t : @wterm psort_notion) :=
    match t with
    | wRel n => wRel n
    | wSort s => wSort (instantiate_sort inst s)
    | wProd A B => wProd (f A) (f B)
    | wLambda A t => wLambda (f A) (f t)
    | wApp u v => wApp (f u) (f v)
    | wSum A B => wSum (f A) (f B)
    | wPair A B u v => wPair (f A) (f B) (f u) (f v)
    | wPi1 A B p => wPi1 (f A) (f B) (f p)
    | wPi2 A B p => wPi2 (f A) (f B) (f p)
    | wEq A u v => wEq (f A) (f u) (f v)
    | wRefl A u => wRefl (f A) (f u)
    | wJ A u P w v p => wJ (f A) (f u) (f P) (f w) (f v) (f p)
    | wTransport A B p t => wTransport (f A) (f B) (f p) (f t)
    | wBeta t u => wBeta (f t) (f u)
    | wK A u p => wK (f A) (f u) (f p)
    | wFunext g h p => wFunext (f g) (f h) (f p)
    | wJBeta u P w => wJBeta (f u) (f P) (f w)
    | wTransportBeta A t => wTransportBeta (f A) (f t)
    | wPairEta p => wPairEta (f p)
    | wProdExt A p => wProdExt (f A) (f p)
    | wSumExt A p => wSumExt (f A) (f p)
    | wConst id => wConst id
    | wDelta id => wDelta id
    end.

Fixpoint instantiate_sorts_ctx `{ S : Sorts.notion }
         (inst : nat -> @sort S)
         (Γ : @wcontext psort_notion)
  : @wcontext S :=
  match Γ with
  | A :: Γ => instantiate_sorts inst A :: instantiate_sorts_ctx inst Γ
  | nil => nil
  end.

Lemma instantiate_sorts_lift :
  forall `{ S : Sorts.notion } inst t n k,
    instantiate_sorts inst (lift n k t) =
    lift n k (instantiate_sorts inst t).
Proof.
  intros S inst t.
  induction t ; intros m k.
  all: try (cbn ; erewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?IHt4, ?IHt5, ?IHt6 ; reflexivity).
  cbn. case_eq (k <=? n) ; intro ; reflexivity.
Defined.

Lemma instantiate_sorts_subst :
  forall `{ S : Sorts.notion } inst t u n,
    instantiate_sorts inst (t{ n := u }) =
    (instantiate_sorts inst t){ n := instantiate_sorts inst u }.
Proof.
  intros S inst t.
  induction t ; intros u m.
  all: try (cbn ; erewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?IHt4, ?IHt5, ?IHt6 ; reflexivity).
  cbn. case_eq (m ?= n).
  - intros _. eapply instantiate_sorts_lift.
  - intros _. reflexivity.
  - intros _. reflexivity.
Defined.

Lemma instantiate_sorts_ctx_length :
  forall `{ S : Sorts.notion } inst Γ,
    #|instantiate_sorts_ctx inst Γ| = #|Γ|.
Proof.
  intros S inst Γ.
  induction Γ ; cbn ; auto.
Defined.

Definition instantiate_sorts_decl `{ S : Sorts.notion } inst
           (d : @glob_decl psort_notion) : @glob_decl S :=
  {| dname := d.(dname) ;
     dtype := instantiate_sorts inst d.(dtype) ;
     dbody := option_map (instantiate_sorts inst) d.(dbody)
  |}.

Definition instantiate_sorts_glob `{ S : Sorts.notion } inst
           (Σ : @wglobal_context psort_notion) : @wglobal_context S :=
  map (instantiate_sorts_decl inst) Σ.

Lemma instantiate_sorts_lookup_glob :
  forall `{ S : Sorts.notion } inst (Σ : @wglobal_context psort_notion) id d,
    lookup_glob Σ id = Some d ->
    let Σ' := instantiate_sorts_glob inst Σ in
    lookup_glob Σ' id = Some (instantiate_sorts_decl inst d).
Proof.
  intros S inst Σ id ty h Σ'.
  induction Σ.
  - cbn in *. discriminate h.
  - cbn in *. revert h. case_eq (ident_eq id (dname a)).
    + intros e h. inversion h. subst. reflexivity.
    + intros e h. eapply IHΣ. assumption.
Defined.

Lemma nth_error_instantiate_sorts :
  forall `{ S : Sorts.notion } Γ n A inst,
    nth_error Γ n = Some A ->
    nth_error (instantiate_sorts_ctx inst Γ) n =
    Some (instantiate_sorts inst A).
Proof.
  intros S Γ n A inst e.
  induction Γ in A, n, e |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in e. inversion e. subst. clear e.
    cbn. reflexivity.
  - cbn in e. eapply IHΓ in e. cbn. assumption.
Defined.

Lemma instantiate_sorts_decl_body :
  ∀ `{ S : Sorts.notion } d t inst,
    dbody d = Some t →
    dbody (instantiate_sorts_decl inst d) = Some (instantiate_sorts inst t).
Proof.
  intros SN d t inst h.
  destruct d. simpl in *.
  subst. reflexivity.
Defined.

Lemma instantiate_sorts_sound :
  forall `{ S : Sorts.notion } Σ Γ inst t A,
    Σ ;;; Γ |-w t : A ->
    let Σ' := instantiate_sorts_glob inst Σ in
    let Γ' := instantiate_sorts_ctx inst Γ in
    let t' := instantiate_sorts inst t in
    let A' := instantiate_sorts inst A in
    type_glob Σ' ->
    wf Σ' Γ' ->
    Σ' ;;; Γ' |-w t' : A'.
Proof.
  intros S Σ Γ inst t A h Σ' Γ' t' A' hg' hw'.
  induction h.
  all: try solve [
             cbn ; econstructor ;
             try (eapply IHh ; eassumption) ;
             try (eapply IHh1 ; eassumption) ;
             try (eapply IHh2 ; eassumption) ;
             try (eapply IHh3 ; eassumption) ;
             try (eapply IHh4 ; eassumption) ;
             try (eapply IHh5 ; eassumption) ;
             try (eapply IHh6 ; eassumption)
           ].
  - cbn. unfold A'.
    rewrite instantiate_sorts_lift.
    econstructor.
    + assumption.
    + unfold Γ'. apply nth_error_instantiate_sorts.
      assumption.
  - cbn. econstructor. assumption.
  - cbn. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. cbn. econstructor ; try assumption.
      eapply IHh1. assumption.
  - cbn. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2.
      cbn. econstructor ; try assumption.
      eapply IHh1. eassumption.
  - cbn. unfold A'. rewrite instantiate_sorts_subst.
    eapply type_App with (A := instantiate_sorts inst A).
    + eapply IHh1. assumption.
    + eapply IHh2. assumption.
  - cbn. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2.
      cbn. econstructor ; try assumption.
      eapply IHh1. eassumption.
  - cbn. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. cbn. econstructor ; try eassumption.
      eapply IHh1. assumption.
    + eapply IHh3. assumption.
    + rewrite <- instantiate_sorts_subst.
      eapply IHh4. assumption.
  - cbn. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. assumption.
    + eapply IHh3. cbn. econstructor ; try eassumption.
      eapply IHh2. assumption.
  - cbn. unfold A'. rewrite instantiate_sorts_subst.
    econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. assumption.
    + eapply IHh3. cbn. econstructor ; try eassumption.
      eapply IHh2. assumption.
  - cbn. unfold A'. rewrite 2!instantiate_sorts_subst.
    econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. assumption.
    + eapply IHh3. assumption.
    + rewrite <- !instantiate_sorts_lift. eapply IHh4.
      cbn. econstructor.
      * econstructor ; try assumption.
        eapply IHh1. assumption.
      * econstructor.
        -- rewrite instantiate_sorts_lift.
           match goal with
           | |- _ ;;; _ |-w _ : ?S =>
             change S with (lift0 1 S)
           end.
           eapply typing_lift01.
           ++ assumption.
           ++ eapply IHh1. assumption.
           ++ eapply IHh1. assumption.
        -- rewrite 2!instantiate_sorts_lift.
           eapply typing_lift01 ; try assumption.
           ++ eapply IHh2. assumption.
           ++ eapply IHh1. assumption.
        -- eapply meta_conv.
           ++ econstructor.
              ** econstructor ; try assumption.
                 eapply IHh1. assumption.
              ** cbn. reflexivity.
           ++ cbn. rewrite instantiate_sorts_lift. reflexivity.
    + eapply IHh5. assumption.
    + rewrite 2!instantiate_sorts_subst in IHh6. eapply IHh6. assumption.
  - cbn. rewrite !instantiate_sorts_subst. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. cbn. econstructor ; try assumption.
      eapply IHh1. assumption.
    + eapply IHh3. assumption.
  - cbn. econstructor.
    + cbn in IHh1. rewrite !instantiate_sorts_lift in IHh1.
      eapply IHh1. assumption.
    + eapply IHh2. assumption.
    + eapply IHh3. assumption.
  - cbn. rewrite 2!instantiate_sorts_subst.
    econstructor.
    + eapply IHh1. assumption.
    + cbn in IHh2. rewrite !instantiate_sorts_lift in IHh2. eapply IHh2.
      repeat eapply wf_snoc ; try eassumption.
      * eapply IHh4. assumption.
      * econstructor.
        -- match goal with
           | |- _ ;;; _ |-w _ : ?S =>
             change S with (lift0 1 S)
           end.
           eapply typing_lift01 ; try eassumption.
           all: eapply IHh4 ; assumption.
        -- eapply typing_lift01 ; try eassumption.
           ++ eapply IHh1 ; assumption.
           ++ eapply IHh4 ; assumption.
        -- econstructor ; try eassumption.
           ++ econstructor ; try eassumption.
              eapply IHh4 ; assumption.
           ++ reflexivity.
    + rewrite 2!instantiate_sorts_subst in IHh3. eapply IHh3. assumption.
    + eapply IHh4 ; assumption.
  - cbn. econstructor.
    + eapply IHh1. cbn. econstructor ; try assumption.
      eapply IHh2. assumption.
    + eapply IHh2. assumption.
  - cbn. econstructor.
    + eapply IHh1. cbn. econstructor ; try assumption.
      eapply IHh2. assumption.
    + eapply IHh2. assumption.
  - eapply meta_conv. econstructor. assumption.
    eapply instantiate_sorts_lookup_glob. eassumption.
    reflexivity.
  - eapply meta_conv.
    + econstructor.
      * assumption.
      * eapply instantiate_sorts_lookup_glob. eassumption.
      * eapply instantiate_sorts_decl_body. eassumption.
    + reflexivity.
Defined.

End PolymorphicSorts.