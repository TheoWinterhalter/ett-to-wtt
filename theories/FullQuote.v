(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template
Require Import Ast utils monad_utils LiftSubst Typing Checker.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping Quotes 
               FinalTranslation.
Import MonadNotation.

Inductive fq_error :=
| NotEnoughFuel
| NotHandled (t : term)
| TypingError (msg : string) (e : type_error) (Γ : context) (t : term)
| WrongType (wanted : string) (got : term)
| UnknownInductive (id : string)
| UnknownConst (id : string)
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
         (indt : assoc sterm) (constt : assoc sterm) {struct fuel}
  : fq_result sterm :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n)
    | tSort _ => ret (sSort tt)
    | tProd nx A B =>
      A' <- fullquote fuel Σ Γ A indt constt ;;
      B' <- fullquote fuel Σ (Γ ,, vass nx A) B indt constt ;;
      ret (sProd nx A' B')
    | tLambda nx A t =>
      match infer_hnf fuel Σ (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ Γ A indt constt ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B indt constt ;;
        t' <- fullquote fuel Σ (Γ ,, vass nx A) t indt constt ;;
        ret (sLambda nx A' B' t')
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    | tApp (tConst "Translation.Quotes.candidate" []) [ _ ; _ ; t ] =>
      fullquote fuel Σ Γ t indt constt
    | tInd {| inductive_mind := id ; inductive_ind := _ |} [] =>
      match assoc_at id indt with
      | Some t => ret t
      | None => raise (UnknownInductive id)
      end
    | tConst id [] =>
      match assoc_at id constt with
      | Some t => ret t
      | None => raise (UnknownConst id)
      end
    | tApp (tInd {| inductive_mind := "Translation.util.pp_sigT"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A indt constt ;;
      B' <- fullquote fuel Σ Γ B indt constt ;;
      ret (sSum nAnon A' (sApp (lift0 1 B') (lift0 1 A') (sSort tt) (sRel 0)))
    (* We cannot quote both ∑ and * to Σ-types *)
    (* | tApp (tInd {| inductive_mind := "Translation.util.pp_prod"; inductive_ind := 0 |} []) [ A ; B ] => *)
    (*   A' <- fullquote fuel Σ Γ A  ;; *)
    (*   let '(A') := A' in *)
    (*   B' <- fullquote fuel Σ Γ B  ;; *)
    (*   let '(B') := B' in *)
    (*   ret (sSum nAnon A' (lift0 1 B')) *)
    | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [ A ; u ; v ] =>
      A' <- fullquote fuel Σ Γ A indt constt ;;
      u' <- fullquote fuel Σ Γ u indt constt ;;
      v' <- fullquote fuel Σ Γ v indt constt ;;
      ret (sEq A' u' v')
    | tApp u [] =>
      fullquote fuel Σ Γ u indt constt
    | tApp u [ v ] =>
      match infer_hnf fuel Σ Γ u with
      | Checked (tProd nx A B) =>
        u' <- fullquote fuel Σ Γ u indt constt ;;
        A' <- fullquote fuel Σ Γ A indt constt ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B indt constt ;;
        v' <- fullquote fuel Σ Γ v indt constt ;;
        ret (sApp u' A' B' v')
      | Checked T => raise (WrongType "Prod" T)
      | TypeError e => raise (TypingError "App1" e Γ u)
      end
    | tApp u (v :: l) =>
      fullquote fuel Σ Γ (tApp (tApp u [ v ]) l) indt constt
    | tCast t _ _ => fullquote fuel Σ Γ t indt constt
    | _ => raise (NotHandled t)
    end
  end.
