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
    getsort =<< wttinfer Σ Γ A ;;
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

Ltac remove1 :=
  match goal with
  | |- context [ match ?t with _ => _ end ] =>
    case_eq t ; try solve [ intros ; discriminate ]
  end.

Ltac go :=
  repeat remove1.

Lemma wttinfer_sound :
  forall Σ Γ t A,
    wttinfer Σ Γ t = Some A ->
    type_glob Σ ->
    wf Σ Γ ->
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
  - cbn in eq. revert eq. go.
    intros T2 eT2 s2 es2 T1 eT1 s1 es1 eq.
    inversion eq. subst. clear eq.
    specialize (IHt1 _ _ eT1).
    specialize (IHt2 _ _ eT2).
    econstructor.
    + destruct T1 ; try discriminate es1.
      cbn in es1. inversion es1. subst.
      auto.
    + destruct T2 ; try discriminate es2.
      cbn in es2. inversion es2. subst.
      eapply IHt2. econstructor ; try assumption.
      destruct T1 ; try discriminate es1.
      cbn in es1. inversion es1. subst.
      auto.
  - cbn in eq. revert eq. go.
    intros w H t H0 s es eq.
    inversion eq. subst. clear eq.
    destruct t ; try discriminate es.
    inversion es. subst. clear es.
    econstructor. eapply IHt2 ; try assumption.
    econstructor ; try eassumption.
    eapply IHt1 ; eassumption.
  - cbn in eq. revert eq. go.
    intros. revert eq. go.
    intros u H2 eq.
    inversion eq. subst. clear eq.
Admitted.

End Checking.

Section PolymorphicSorts.

(* Polymorhpic sorts *)
Inductive psort :=
| pvar (n : nat)
| psucc (s : psort)
| pprod_sort (s1 s2 : psort)
| psum_sort (s1 s2 : psort)
| peq_sort (s : psort)
.

Instance psort_notion : Sorts.notion := {|
  sort := psort ;
  succ := psucc ;
  prod_sort := pprod_sort ;
  sum_sort := psum_sort ;
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
    | wFunext A B g h p => wFunext (f A) (f B) (f g) (f h) (f p)
    | wHeq A a B b => wHeq (f A) (f a) (f B) (f b)
    | wHeqPair p q => wHeqPair (f p) (f q)
    | wHeqTy A B p => wHeqTy (f A) (f B) (f p)
    | wHeqTm p => wHeqTm (f p)
    | wPack A1 A2 => wPack (f A1) (f A2)
    | wProjT1 p => wProjT1 (f p)
    | wProjT2 p => wProjT2 (f p)
    | wProjTe p => wProjTe (f p)
    | wAx id => wAx id
    end.

Fixpoint instantiate_sorts_ctx `{ S : Sorts.notion }
         (inst : nat -> @sort S)
         (Γ : @wcontext psort_notion)
  : @wcontext S :=
  match Γ with
  | A :: Γ => instantiate_sorts inst A :: instantiate_sorts_ctx inst Γ
  | nil => nil
  end.

Lemma instantiate_sorts_sound :
  forall `{ S : Sorts.notion } Σ Γ inst t A,
    Σ ;;; Γ |-w t : A ->
    let Γ' := instantiate_sorts_ctx inst Γ in
    let t' := instantiate_sorts inst t in
    let A' := instantiate_sorts inst A in
    wf Σ Γ' ->
    Σ ;;; Γ' |-w t' : A'.
Proof.
  intros S Σ Γ inst t A h Γ' t' A' hw'.
  induction h.
  - cbn. admit.
  - cbn. econstructor. assumption.
  - cbn. econstructor.
    + eapply IHh1. assumption.
    + eapply IHh2. cbn. econstructor ; try assumption.
      eapply IHh1. assumption.
  - cbn. econstructor. eapply IHh.
    cbn. econstructor ; try assumption.
Abort.

End PolymorphicSorts.