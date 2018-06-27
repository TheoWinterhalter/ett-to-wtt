(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template
Require Import Ast utils monad_utils LiftSubst Typing Checker.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping Quotes FinalTranslation.

Import MonadNotation.

Inductive fq_error :=
| NotEnoughFuel
| NotHandled
| TypingError (msg : string) (e : type_error) (Γ : context) (t : term)
| WrongType (wanted : string) (got : term)
.

Inductive fq_result A :=
| Success : A -> fq_result A
| Error : fq_error -> fq_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance fq_monad : Monad fq_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc fq_error fq_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Close Scope s_scope.

Local Existing Instance Sorts.type_in_type.

Fixpoint fullquote (fuel : nat) (Σ : global_context) (Γ : context) (t : term)
         {struct fuel} : fq_result sterm :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n)
    | tSort _ => ret (sSort tt)
    | tProd nx A B =>
      A' <- fullquote fuel Σ Γ A ;;
      B' <- fullquote fuel Σ (Γ ,, vass nx A) B  ;;
      ret (sProd nx A' B')
    | tLambda nx A t =>
      match infer_hnf fuel Σ (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ Γ A ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B ;;
        t' <- fullquote fuel Σ (Γ ,, vass nx A) t ;;
        ret (sLambda nx A' B' t')
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    (* The following examples should be handled more generically,
       with a correspondance table. [TODO]
     *)
    | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [] =>
      ret (sAx "nat")
    | tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 [] =>
      ret (sAx "zero")
    | tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [] =>
      ret (sAx "succ")
    | tConst "Coq.Init.Datatypes.nat_rect" [] =>
      ret (sAx "nat_rect")
    | tConst "Coq.Init.Datatypes.nat_rect_zero" [] =>
      ret (sAx "nat_rect_zero")
    | tConst "Coq.Init.Datatypes.nat_rect_succ" [] =>
      ret (sAx "nat_rect_succ")
    | tInd {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |} [] =>
      ret (sAx "vec")
    | tConstruct {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |} 0 [] =>
      ret (sAx "vnil")
    | tConstruct {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |} 1 [] =>
      ret (sAx "vcons")
    | tConst "Translation.Quotes.vec_rect" [] =>
      ret (sAx "vec_rect")
    (* Resuming *)
    | tApp (tInd {| inductive_mind := "Translation.util.pp_sigT"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A  ;;
      B' <- fullquote fuel Σ Γ B  ;;
      ret (sSum nAnon A' (sApp (lift0 1 B') (lift0 1 A') (sSort tt) (sRel 0)))
    (* We cannot quote both ∑ and * to Σ-types *)
    (* | tApp (tInd {| inductive_mind := "Translation.util.pp_prod"; inductive_ind := 0 |} []) [ A ; B ] => *)
    (*   A' <- fullquote fuel Σ Γ A  ;; *)
    (*   let '(A') := A' in *)
    (*   B' <- fullquote fuel Σ Γ B  ;; *)
    (*   let '(B') := B' in *)
    (*   ret (sSum nAnon A' (lift0 1 B')) *)
    | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [ A ; u ; v ] =>
      A' <- fullquote fuel Σ Γ A  ;;
      u' <- fullquote fuel Σ Γ u  ;;
      v' <- fullquote fuel Σ Γ v  ;;
      ret (sEq A' u' v')
    | tApp u [] =>
      fullquote fuel Σ Γ u 
    | tApp u [ v ] =>
      match infer_hnf fuel Σ Γ u with
      | Checked (tProd nx A B) =>
        u' <- fullquote fuel Σ Γ u  ;;
        A' <- fullquote fuel Σ Γ A  ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B  ;;
        v' <- fullquote fuel Σ Γ v  ;;
        ret (sApp u' A' B' v')
      | Checked T => raise (WrongType "Prod" T)
      | TypeError e => raise (TypingError "App1" e Γ u)
      end
    | tApp u (v :: l) =>
      fullquote fuel Σ Γ (tApp (tApp u [ v ]) l) 
    | _ => raise NotHandled
    end
  end.
