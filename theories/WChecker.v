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

Definition assert_true (b : bool) : option unit :=
  if b then ret tt else None.

Definition assert_eq (u v : wterm) :=
  assert_true (eq_term u v).

Definition assert_eq_sort (s1 s2 : sort) : option unit :=
  if Sorts.eq_dec s1 s2 then ret tt else None.

Fixpoint _wttinfer (Σ : wglobal_context) (Γ : wcontext) (t : wterm)
  : option wterm :=
  match t with
  | wRel n => nth_error Γ n
  | wSort s => ret (wSort (succ s))
  | wProd n A B =>
    s1 <- getsort =<< _wttinfer Σ Γ A ;;
    s2 <- getsort =<< _wttinfer Σ (Γ ,, A) B ;;
    ret (wSort (prod_sort s1 s2))
  | wLambda n A t =>
    (* _ <- getsort =<< _wttinfer Σ Γ A ;; *)
    B <- _wttinfer Σ (Γ ,, A) t ;;
    ret (wProd n A B)
  | wApp u v =>
    Π <- getprod =<< _wttinfer Σ Γ u ;;
    let '(A,B) := Π in
    assert_eq A =<< _wttinfer Σ Γ v ;;
    ret (B{ 0 := u })
  (* TODO Σ *)
  | wEq A u v =>
    s <- getsort =<< _wttinfer Σ Γ A ;;
    assert_eq A =<< _wttinfer Σ Γ u ;;
    assert_eq A =<< _wttinfer Σ Γ v ;;
    ret (wSort (eq_sort s))
  | wRefl A u =>
    getsort =<< _wttinfer Σ Γ A ;;
    assert_eq A =<< _wttinfer Σ Γ u ;;
    ret (wEq A u u)
  | wJ A u P w v p =>
    getsort =<< _wttinfer Σ Γ A ;;
    assert_eq A =<< _wttinfer Σ Γ u ;;
    assert_eq A =<< _wttinfer Σ Γ v ;;
    getsort =<< _wttinfer Σ (Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0))) P ;;
    assert_eq (wEq A u v) =<< _wttinfer Σ Γ p ;;
    assert_eq (P{ 1 := u }{ 0 := wRefl A u }) =<< _wttinfer Σ Γ w ;;
    ret (P{ 1 := v }{ 0 := p })
  | wTransport A B p t =>
    s <- getsort =<< _wttinfer Σ Γ A ;;
    assert_eq_sort s =<< getsort =<< _wttinfer Σ Γ B ;;
    assert_eq (wEq (wSort s) A B) =<< _wttinfer Σ Γ p ;;
    assert_eq A =<< _wttinfer Σ Γ t ;;
    ret B
  | _ => None
  end.

End Checking.