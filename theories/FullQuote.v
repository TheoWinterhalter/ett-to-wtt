(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template
Require Import Ast utils monad_utils LiftSubst Typing Checker Template.
From Translation
Require Import util SAst SLiftSubst SCommon ITyping Quotes FinalTranslation.

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

Fixpoint fullquote (fuel : nat) (Σ : global_context) (Γ : context) (t : term)
         (sf : nat -> sort) (si : nat)
         {struct fuel} : fq_result (sterm * nat) :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n, si)
    | tSort u => ret (sSort (sf si), S si)
    | tProd nx A B =>
      A' <- fullquote fuel Σ Γ A sf si ;;
      let '(A', si) := A' in
      B' <- fullquote fuel Σ (Γ ,, vass nx A) B sf si ;;
      let '(B', si) := B' in
      ret (sProd nx A' B', si)
    | tLambda nx A t =>
      match infer_hnf fuel Σ (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ Γ A sf si ;;
        let '(A', si) := A' in
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B sf si ;;
        let '(B', si) := B' in
        t' <- fullquote fuel Σ (Γ ,, vass nx A) t sf si ;;
        let '(t', si) := t' in
        ret (sLambda nx A' B' t', si)
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    (* The following examples should be handled more generically? *)
    | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [] =>
      ret (sAx "nat", si)
    | tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 [] =>
      ret (sAx "zero", si)
    | tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [] =>
      ret (sAx "succ", si)
    | tConst "Coq.Init.Datatypes.nat_rect" [] =>
      ret (sAx "nat_rect", si)
    | tConst "Coq.Init.Datatypes.nat_rect_zero" [] =>
      ret (sAx "nat_rect_zero", si)
    | tConst "Coq.Init.Datatypes.nat_rect_succ" [] =>
      ret (sAx "nat_rect_succ", si)
    | tInd {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |} [] =>
      ret (sAx "vec", si)
    | tConstruct {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |} 0 [] =>
      ret (sAx "vnil", si)
    | tConstruct {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |} 1 [] =>
      ret (sAx "vcons", si)
    | tConst "Translation.Quotes.vec_rect" [] =>
      ret (sAx "vec_rect", si)
    (* Resuming *)
    | tApp (tInd {| inductive_mind := "Translation.util.pp_sigT"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A sf si ;;
      let '(A', si) := A' in
      B' <- fullquote fuel Σ Γ B sf si ;;
      let '(B', si) := B' in
      ret (sSum nAnon A' (sApp (lift0 1 B') (lift0 1 A') (sSort (sf si)) (sRel 0)), S si)
    (* We cannot quote both ∑ and * to Σ-types *)
    (* | tApp (tInd {| inductive_mind := "Translation.util.pp_prod"; inductive_ind := 0 |} []) [ A ; B ] => *)
    (*   A' <- fullquote fuel Σ Γ A sf si ;; *)
    (*   let '(A', si) := A' in *)
    (*   B' <- fullquote fuel Σ Γ B sf si ;; *)
    (*   let '(B', si) := B' in *)
    (*   ret (sSum nAnon A' (lift0 1 B'), si) *)
    | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [ A ; u ; v ] =>
      A' <- fullquote fuel Σ Γ A sf si ;;
      let '(A', si) := A' in
      u' <- fullquote fuel Σ Γ u sf si ;;
      let '(u', si) := u' in
      v' <- fullquote fuel Σ Γ v sf si ;;
      let '(v', si) := v' in
      ret (sEq A' u' v', si)
    | tApp u [] =>
      fullquote fuel Σ Γ u sf si
    | tApp u [ v ] =>
      match infer_hnf fuel Σ Γ u with
      | Checked (tProd nx A B) =>
        u' <- fullquote fuel Σ Γ u sf si ;;
        let '(u', si) := u' in
        A' <- fullquote fuel Σ Γ A sf si ;;
        let '(A', si) := A' in
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B sf si ;;
        let '(B', si) := B' in
        v' <- fullquote fuel Σ Γ v sf si ;;
        let '(v', si) := v' in
        ret (sApp u' A' B' v', si)
      | Checked T => raise (WrongType "Prod" T)
      | TypeError e => raise (TypingError "App1" e Γ u)
      end
    | tApp u (v :: l) =>
      fullquote fuel Σ Γ (tApp (tApp u [ v ]) l) sf si
    | _ => raise NotHandled
    end
  end.
