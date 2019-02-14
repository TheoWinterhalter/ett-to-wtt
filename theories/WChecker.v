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
    nth_error Γ n
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
  (* TODO Σ *)
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
  | _ => None
  end.

End Checking.