(*! Type checker for WTT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
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
  | wProd n A B => ret (A,B)
  | _ => raise (Msg "getprod")
  end.

Definition getsum (T : wterm) : i_result (wterm * wterm) :=
  match T with
  | wSum n A B => ret (A,B)
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
  | wProd n A B =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    s2 <- getsort =<< wttinfer Σ (Γ ,, A) B ;;
    ret (wSort (prod_sort s1 s2))
  | wLambda n A t =>
    getsort =<< wttinfer Σ Γ A ;;
    B <- wttinfer Σ (Γ ,, A) t ;;
    ret (wProd n A B)
  | wApp u v =>
    Π <- getprod =<< wttinfer Σ Γ u ;;
    let '(A,B) := Π in
    assert_eq A =<< wttinfer Σ Γ v ;;
    ret (B{ 0 := v })
  | wSum n A B =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    s2 <- getsort =<< wttinfer Σ (Γ ,, A) B ;;
    ret (wSort (sum_sort s1 s2))
  | wPair A B u v =>
    getsort =<< wttinfer Σ Γ A ;;
    getsort =<< wttinfer Σ (Γ,, A) B ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    assert_eq (B{ 0 := u }) =<< wttinfer Σ Γ v ;;
    ret (wSum nAnon A B)
  | wPi1 A B p =>
    assert_eq (wSum nAnon A B) =<< wttinfer Σ Γ p ;;
    getsort =<< wttinfer Σ Γ A ;;
    getsort =<< wttinfer Σ (Γ,, A) B ;;
    ret A
  | wPi2 A B p =>
    assert_eq (wSum nAnon A B) =<< wttinfer Σ Γ p ;;
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
    ret (wEq (B{ 0 := u }) (wApp (wLambda nAnon A t) u) (t{ 0 := u }))
  | wK A u p =>
    getsort =<< wttinfer Σ Γ A ;;
    assert_eq A =<< wttinfer Σ Γ u ;;
    assert_eq (wEq A u u) =<< wttinfer Σ Γ p ;;
    ret (wEq (wEq A u u) p (wRefl A u))
  | wFunext f g p =>
    Π <- getprod =<< wttinfer Σ Γ f ;;
    let '(A,B) := Π in
    assert_eq (wProd nAnon A B) =<< wttinfer Σ Γ g ;;
    assert_eq (wProd nAnon A
                 (wEq B (wApp (lift0 1 f) (wRel 0))
                        (wApp (lift0 1 g) (wRel 0))))
              =<< wttinfer Σ Γ p ;;
    ret (wEq (wProd nAnon A B) f g)
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
    ret (wEq (wSum nAnon A B) (wPair A B (wPi1 A B p) (wPi2 A B p)) p)
  | wProdExt A p =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    E <- geteq =<< wttinfer Σ (Γ,, A) p ;;
    let '(S2,B1,B2) := E in
    s2 <- getsort S2 ;;
    ret (wEq (wSort (prod_sort s1 s2)) (wProd nAnon A B1) (wProd nAnon A B2))
  | wSumExt A p =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    E <- geteq =<< wttinfer Σ (Γ,, A) p ;;
    let '(S2,B1,B2) := E in
    s2 <- getsort S2 ;;
    ret (wEq (wSort (sum_sort s1 s2)) (wSum nAnon A B1) (wSum nAnon A B2))
  | wAx id =>
    match lookup_glob Σ id with
    | Some d => ret (dtype d)
    | None  => raise (Msg ("unknown constant: " ++ id))
    end
  | wDelta id =>
    match lookup_glob Σ id with
    | Some d => ret (wEq (dtype d) (wAx id) (dbody d))
    | None  => raise (Msg ("unknown constant: " ++ id))
    end
  end.

Lemma type_Beta' :
  forall {Σ Γ A B t u n},
    type_glob Σ ->
    Σ ;;; Γ,, A |-w t : B ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wBeta t u
             : wEq (B {0 := u}) (wApp (wLambda n A t) u) (t {0 := u}).
Proof.
  intros Σ Γ A B t u n hg ht hu.
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
  eapply type_rename ; [
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
  - cbn in eq. revert eq. case_eq (nth_error Γ n).
    + intros A' eq e. inversion e. subst.
      eapply meta_conv.
      * eapply type_Rel. assumption.
      * erewrite (nth_error_Some_safe_nth eq). reflexivity.
    + intros H eq. discriminate eq.
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
           ++ econstructor. econstructor ; try eassumption. ih.
           ++ cbn. reflexivity.
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
      * econstructor. econstructor ; eassumption.
      * cbn. reflexivity.
  Unshelve.
  all: try solve [ constructor ].
  { cbn. auto with arith. }
  { cbn. auto with arith. }
Defined.

Lemma nth_error_rename :
  forall {Γ Δ n A},
    nth_error Γ n = Some A ->
    nlctx Γ = nlctx Δ ->
    exists B, nth_error Δ n = Some B /\ nl A = nl B.
Proof.
  intros Γ Δ n A h eq. revert Δ n A h eq.
  induction Γ ; intros Δ n A h eq.
  - destruct n ; simpl in h ; discriminate.
  - destruct Δ ; simpl in eq ; try discriminate eq.
    destruct n.
    + cbn in h. inversion h. subst. clear h.
      inversion eq.
      cbn. eexists. split.
      * reflexivity.
      * assumption.
    + cbn in h. cbn. eapply IHΓ.
      * assumption.
      * inversion eq. reflexivity.
Defined.

Ltac nleq :=
  repeat (try eapply nl_lift ; try eapply nl_subst) ;
  cbn ; auto ; f_equal ; eauto.

Ltac rewwtt :=
  lazymatch goal with
  | ih : _ -> _ -> _ -> _ -> _ -> exists _, wttinfer _ _ ?t = _ /\ _,
    h : wttinfer _ ?Γ ?t = _,
    e : nlctx ?Γ = nlctx ?Δ
    |- context [ wttinfer _ ?Δ ?t ] =>
      let eq := fresh "eq" in
      destruct (ih _ _ _ h e) as [? [eq ?]] ;
      rewrite eq
  | ih : _ -> _ -> _ -> _ -> _ -> exists _, wttinfer _ _ ?t = _ /\ _,
    h : wttinfer _ ?Γ ?t = _
    |- context [ wttinfer _ ?Δ ?t ] =>
      let e := fresh "e" in
      assert (nlctx Γ = nlctx Δ) as e ; [
        repeat nleq
      | let eq := fresh "eq" in
        destruct (ih _ _ _ h e) as [? [eq ?]] ;
        rewrite eq
      ]
  end.

Ltac cbn_nl :=
  match goal with
  | h : nl (wSort _) = _ |- _ =>
    cbn in h
  | h : nl (wProd _ _ _) = _ |- _ =>
    cbn in h
  | h : nl (wEq _ _ _) = _ |- _ =>
    cbn in h
  | h : nl (wSum _ _ _) = _ |- _ =>
    cbn in h
  end.

Ltac inv_nl :=
  match goal with
  | h : nlSort _ = nl ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  | h : nlProd _ _ = nl ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  | h : nlSum _ _ = nl ?t |- _ =>
    destruct t ; cbn in h ; try discriminate h ;
    inversion h ; subst ; clear h
  | h : nlEq _ _ _ = nl ?t |- _ =>
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

Lemma wttinfer_rename_ctx :
  forall {Σ Γ Δ t A},
    wttinfer Σ Γ t = Success A ->
    nlctx Γ = nlctx Δ ->
    exists B, wttinfer Σ Δ t = Success B /\ nl A = nl B.
Proof.
  intros Σ Γ Δ t A h eq. revert Γ Δ A h eq.
  induction t ; intros Γ Δ A h eq.
  all: try solve [
    go h ; simpl ;
    repeat rewwtt ;
    repeat (cbn_nl ; inv_nl) ;
    repeat inv_nl ;
    simpl ;
    unfold assert_eq ;
    rewrite ?assert_eq_sort_refl ;
    repeat (erewrite (proj2 eq_term_spec) ; [| shelve]) ;
    simpl ;
    eexists ; split ; [ reflexivity | repeat nleq ]
  ].
  - simpl in h. simpl. revert h. case_eq (nth_error Γ n).
    + intros B e h. inversion h. subst. clear h.
      destruct (nth_error_rename e eq) as [? [ee ?]].
      rewrite ee.
      eexists. split.
      * reflexivity.
      * eapply nl_lift. assumption.
    + intros e h. discriminate h.
  - simpl in h. simpl.
    eexists. split.
    + eassumption.
    + reflexivity.
  - simpl in h. simpl.
    eexists. split.
    + eassumption.
    + reflexivity.
  Unshelve.
  all: repeat match goal with
              | h : eq_term _ _ = true |- _ =>
                apply eq_term_spec in h
              end.
  all: try solve [
    match goal with
    | h : nl ?x = nl ?y |- nl _ = nl ?y =>
      transitivity (nl x) ; eauto
    end
  ].
  * transitivity (nl w0_1) ; eauto. transitivity (nl w) ; eauto.
  * transitivity (nl w0) ; eauto.
    transitivity (nl (wProd nAnon w1_1 w1_2)) ; eauto.
    nleq.
  * transitivity (nl w) ; eauto.
    match goal with
    | h : nl ?x = nl ?y |- nl _ = nl ?y =>
      transitivity (nl x) ; eauto
    end.
    cbn. f_equal.
    -- eauto.
    -- f_equal. eauto.
  * repeat match goal with
    | h : nl ?x = nl ?y |- nl _ = nl ?y =>
      transitivity (nl x) ; eauto
    end.
    repeat nleq.
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
  repeat cbn_nl ;
  repeat inv_nl ;
  simpl ;
  unfold assert_eq ;
  rewrite ?assert_eq_sort_refl ;
  repeat (erewrite (proj2 eq_term_spec) ; [| shelve]) ;
  simpl ;
  eexists ; split ; [
    reflexivity
  | repeat nleq
  ].

Lemma wttinfer_complete :
  forall {Σ Γ t A},
    Σ ;;; Γ |-w t : A ->
    exists B, wttinfer Σ Γ t = Success B /\ nl A = nl B.
Proof.
  intros Σ Γ t A h.
  induction h.
  all: try solve [ co ].
  - exists (lift0 (S n) (safe_nth Γ (exist _ n isdecl))). split.
    + cbn. erewrite nth_error_safe_nth. reflexivity.
    + reflexivity.
  - simpl.
    repeat rewih.
    assert (nlctx (Γ,, A) = nlctx (Γ,, x)) as eq.
    { cbn. f_equal. assumption. }
    destruct (wttinfer_rename_ctx e0 eq) as [? [e3 ?]].
    rewrite e3.
    repeat cbn_nl.
    repeat inv_nl.
    simpl.
    unfold assert_eq.
    rewrite ?assert_eq_sort_refl.
    repeat (erewrite (proj2 eq_term_spec) ; [| shelve]).
    simpl.
    eexists. split.
    + reflexivity.
    + cbn. f_equal.
      * eapply nl_subst ; try reflexivity.
        transitivity (nl x0) ; eauto.
      * repeat nleq.
  - simpl.
    repeat rewih.
    assert (nlctx ((Γ,, A),, wEq (↑ A) (↑ u) (wRel 0))
            = nlctx ((Γ,, x2),, wEq (↑ x2) (↑ u) (wRel 0))) as eq.
    { cbn. f_equal.
      - f_equal. eapply nl_lift. assumption.
      - f_equal. assumption.
    }
    destruct (wttinfer_rename_ctx e1 eq) as [? [e3 ?]].
    rewrite e3.
    repeat cbn_nl.
    repeat inv_nl.
    repeat cbn_nl.
    repeat inv_nl.
    simpl.
    unfold assert_eq.
    rewrite ?assert_eq_sort_refl.
    repeat (erewrite (proj2 eq_term_spec) ; [| shelve]).
    simpl.
    eexists. split.
    + reflexivity.
    + repeat nleq.
  - simpl. exists (dtype d). split.
    + rewrite_assumption; reflexivity.
    + reflexivity.
  - simpl. exists (wEq (dtype d) (wAx id) (dbody d)). split.
    + rewrite_assumption; reflexivity.
    + reflexivity.
  - rewih. eexists. split.
    + reflexivity.
    + transitivity (nl A) ; eauto.
  Unshelve.
  all: try assumption.
  all: try solve [repeat nleq].
  * transitivity (nl A) ; eauto.
  * cbn. f_equal.
    -- transitivity (nl A) ; eauto.
    -- transitivity (nl B) ; eauto.
  * cbn. f_equal.
    -- transitivity (nl A) ; eauto.
    -- f_equal.
       ++ transitivity (nl B) ; eauto.
       ++ assumption.
       ++ assumption.
  * etransitivity ; [| eassumption].
    eapply nl_subst ; try reflexivity.
    nleq.
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

Instance psort_notion : Sorts.notion := {|
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
    | wProd n A B => wProd n (f A) (f B)
    | wLambda n A t => wLambda n (f A) (f t)
    | wApp u v => wApp (f u) (f v)
    | wSum n A B => wSum n (f A) (f B)
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
    | wAx id => wAx id
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

Lemma instantiate_sorts_safe_nth :
  forall `{ S : Sorts.notion } inst (Γ : @wcontext psort_notion) n is is',
    instantiate_sorts inst (safe_nth Γ (exist _ n is)) =
    safe_nth (instantiate_sorts_ctx inst Γ) (exist _ n is').
Proof.
  intros S inst Γ.
  induction Γ ; intros n is is'.
  - cbn. bang.
  - destruct n.
    + cbn. reflexivity.
    + cbn. erewrite IHΓ. reflexivity.
Defined.


Definition instantiate_sorts_decl `{ S : Sorts.notion } inst
           (d : @glob_decl psort_notion) : @glob_decl S :=
  {| dname := d.(dname) ;
     dtype := instantiate_sorts inst d.(dtype) ;
     dbody := instantiate_sorts inst d.(dbody)
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

Lemma nl_instantiate_sorts :
  forall `{ S : Sorts.notion } inst t u,
    nl t = nl u ->
    nl (instantiate_sorts inst t) = nl (instantiate_sorts inst u).
Proof.
  intros S inst t.
  induction t ; intros u e ; destruct u ; cbn in e ; try discriminate e.
  all:
    try (cbn ; inversion e ;
         repeat (erewrite_assumption by eassumption) ; reflexivity).
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
    unshelve erewrite instantiate_sorts_safe_nth.
    + rewrite instantiate_sorts_ctx_length. assumption.
    + econstructor. assumption.
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
    eapply type_App with (A0 := instantiate_sorts inst A).
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
           ++ econstructor. econstructor ; try assumption.
              eapply IHh1. assumption.
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
        -- eapply meta_conv.
           ++ econstructor ; try eassumption.
              econstructor ; try eassumption.
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
  - eapply meta_conv. econstructor. assumption.
    eapply instantiate_sorts_lookup_glob. eassumption.
    reflexivity.
  - eapply type_rename.
    + eapply IHh. assumption.
    + unfold A'. eapply nl_instantiate_sorts. assumption.
  Unshelve.
  { cbn. auto with arith. }
  { cbn. auto with arith. }
Defined.

End PolymorphicSorts.