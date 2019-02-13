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
  | _ => None
  end.

End Checking.