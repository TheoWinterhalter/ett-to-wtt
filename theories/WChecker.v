(*! Type checker for WTT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import All.
From Translation
Require Import util Sorts WAst WLiftSubst WTyping WEquality.
Import MonadNotation.

Section Checking.

Context `{Sort_notion : Sorts.notion}.

Definition getsort (T : wterm) : option sort :=
  match T with
  | wSort s => ret s
  | _ => None
  end.

Definition getprod (T : wterm) : option (wterm * wterm) :=
  match T with
  | wProd n A B => ret (A,B)
  | _ => None
  end.

Definition geteq (T : wterm) : option (wterm * wterm * wterm) :=
  match T with
  | wEq A u v => ret (A,u,v)
  | _ => None
  end.

Definition gettransport (t : wterm) : option (wterm * wterm * wterm * wterm) :=
  match t with
  | wTransport A B e t => ret (A,B,e,t)
  | _ => None
  end.

Definition getheq (T : wterm) : option (wterm * wterm * wterm * wterm) :=
  match T with
  | wHeq A a B b => ret (A,a,B,b)
  | _ => None
  end.

Definition getpack (T : wterm) : option (wterm * wterm) :=
  match T with
  | wPack A1 A2 => ret (A1,A2)
  | _ => None
  end.

Definition assert_true (b : bool) : option unit :=
  if b then ret tt else None.

Definition assert_eq (u v : wterm) :=
  assert_true (eq_term u v).

Definition assert_eq_sort (s1 s2 : sort) : option unit :=
  if Sorts.eq_dec s1 s2 then ret tt else None.

Fixpoint wttinfer (Σ : wglobal_context) (Γ : wcontext) (t : wterm)
  : option wterm :=
  match t with
  | wRel n =>
     A <- nth_error Γ n ;;
     ret (lift0 (S n) A)
  | wSort s =>
    ret (wSort (succ s))
  | wProd n A B =>
    s1 <- getsort =<< wttinfer Σ Γ A ;;
    s2 <- getsort =<< wttinfer Σ (Γ ,, A) B ;;
    ret (wSort (prod_sort s1 s2))
  | wLambda n A t =>
    (* _ <- getsort =<< wttinfer Σ Γ A ;; *)
    B <- wttinfer Σ (Γ ,, A) t ;;
    ret (wProd n A B)
  | wApp u v =>
    Π <- getprod =<< wttinfer Σ Γ u ;;
    let '(A,B) := Π in
    assert_eq A =<< wttinfer Σ Γ v ;;
    ret (B{ 0 := u })
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
    assert_eq (wEq A u u) =<< wttinfer Σ Γ p ;;
    ret (wEq (wEq A u u) p (wRefl A u))
  | wFunext A B f g p =>
    assert_eq (wProd nAnon A
                 (wEq B (wApp (lift0 2 f) (wRel 0))
                        (wApp (lift0 2 g) (wRel 0))))
              =<< wttinfer Σ Γ p ;;
    ret (wEq (wProd nAnon A B) f g)
  | wHeq A a B b =>
    s <- getsort =<< wttinfer Σ Γ A ;;
    assert_eq_sort s =<< getsort =<< wttinfer Σ Γ B ;;
    assert_eq A =<< wttinfer Σ Γ a ;;
    assert_eq B =<< wttinfer Σ Γ b ;;
    ret (wSort s)
  | wHeqPair p q =>
    E <- geteq =<< wttinfer Σ Γ p ;;
    let '(T,A,B) := E in
    s <- getsort T ;;
    E' <- geteq =<< wttinfer Σ Γ q ;;
    let '(B',ta,b) := E' in
    assert_eq B B' ;;
    ti <- gettransport ta ;;
    let '(A',B',e,a) := ti in
    assert_eq A A' ;;
    assert_eq B B' ;;
    ret (wHeq A a B b)
  | wHeqTy A B p =>
    H <- getheq =<< wttinfer Σ Γ p ;;
    let '(A',a,B',b) := H in
    assert_eq A A' ;;
    assert_eq B B' ;;
    s <- getsort =<< wttinfer Σ Γ A ;;
    assert_eq_sort s =<< getsort =<< wttinfer Σ Γ A ;;
    ret (wEq (wSort s) A B)
  | wHeqTm p =>
    H <- getheq =<< wttinfer Σ Γ p ;;
    let '(A,a,B,b) := H in
    ret (wEq B (wTransport A B (wHeqTy A B p) a) b)
  | wPack A1 A2 =>
    s <- getsort =<< wttinfer Σ Γ A1 ;;
    assert_eq_sort s =<< getsort =<< wttinfer Σ Γ A2 ;;
    ret (wSort s)
  | wProjT1 p =>
    P <- getpack =<< wttinfer Σ Γ p ;;
    let '(A1,A2) := P in
    ret A1
  | wProjT2 p =>
    P <- getpack =<< wttinfer Σ Γ p ;;
    let '(A1,A2) := P in
    ret A2
  | wProjTe p =>
    P <- getpack =<< wttinfer Σ Γ p ;;
    let '(A1,A2) := P in
    ret (wHeq A1 (wProjT1 p) A2 (wProjT2 p))
  | wAx id =>
    lookup_glob Σ id
  end.

Lemma meta_conv :
  forall Σ Γ t A B,
    Σ ;;; Γ |-w t : A ->
    A = B ->
    Σ ;;; Γ |-w t : B.
Proof.
  intros Σ Γ t A B h e.
  destruct e. assumption.
Defined.

Lemma wttinfer_sound :
  forall Σ Γ t A,
    wttinfer Σ Γ t = Some A ->
    type_glob Σ ->
    wf Σ Γ ->
    (* Σ ;;; Γ |-w A : Ty -> *)
    Σ ;;; Γ |-w t : A.
Proof.
  intros Σ Γ t A eq hg hw.
  revert Γ A eq hw.
  induction t ; intros Γ A eq hw.
  - cbn in eq. revert eq. case_eq (nth_error Γ n).
    + intros A' eq e. inversion e. subst.
      eapply meta_conv.
      * eapply type_Rel. assumption.
      * erewrite nth_error_Some_safe_nth with (e := eq). reflexivity.
    + intros H eq. discriminate eq.
  - cbn in eq. inversion eq. subst. clear eq.
    eapply type_Sort. assumption.
  - cbn in eq. revert eq.
    case_eq (wttinfer Σ Γ t1) ; try solve [ intros ; discriminate ].
    intros A' et1. specialize (IHt1 _ _ et1 hw).
    case_eq (getsort A') ; try solve [ intros ; discriminate ].
    intros s es.
Abort.

End Checking.