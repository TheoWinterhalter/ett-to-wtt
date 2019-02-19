(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template
Require Import Ast utils monad_utils Typing Checker.
From Translation
Require Import util Sorts WAst WLiftSubst WTyping WChecker WLemmata Quotes.
From TypingFlags Require Import Loader.
Import MonadNotation ListNotations.


Inductive fq_error :=
| NotEnoughFuel
| NotHandled (t : term)
| TypingError (msg : string) (e : type_error) (Γ : context) (t : term)
| WrongType (wanted : string) (got : term)
| UnknownInductive (id : string)
| UnknownConst (id : string)
| UnknownConstruct (id : string) (n : nat)
| AlgebraicUniverse
| NotEnoughSorts
| InstanciationNotHandeled (c : string) (l : list term)
| MsgError (msg : string)
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


Local Existing Instance psort_notion.
Definition tsl_univ (univs : assoc sort) (u : universe) :=
  match u with
  | [ pair (Level.Level l) (false) ] =>
    match assoc_at l univs with
    | Some t => Success t
    | None  => Error NotEnoughSorts
    end
  | _ => Error AlgebraicUniverse
  end.


Section fq.
Unset Guard Checking.

Context (constt : assoc wterm) (univs : assoc sort).

Fixpoint fullquote (t : term)
         {struct t}
  : fq_result wterm :=
    match t with
    | tRel n => ret (wRel n)
    | tSort u => u' <- tsl_univ univs u ;;
                ret (wSort u')
    | tProd nx A B =>
      A' <- fullquote A ;;
      B' <- fullquote B ;;
      ret (wProd nx A' B')
    | tLambda nx A t =>
      A' <- fullquote A ;;
      t' <- fullquote t ;;
      ret (wLambda nx A' t')
    | tCast t _ _ => fullquote t
    | tConst id univs => fullquote (tApp (tConst id univs) [])
    | tApp (tConst c _) l =>
      if eq_string c "Translation.Quotes.sigT" then
        match l with
        | [A; tLambda nx _ B] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          ret (wSum nx A' B')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.existT" then
        match l with
        | [A; tLambda nx _ B; u; v] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          u' <- fullquote u ;;
          v' <- fullquote v ;;
          ret (wPair A' B' u' v')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.projT1" then
        match l with
        | [A; tLambda nx _ B; u] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          u' <- fullquote u ;;
          ret (wPi1 A' B' u')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.projT2" then
        match l with
        | [A; tLambda nx _ B; u] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          u' <- fullquote u ;;
          ret (wPi2 A' B' u')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.eq" then
        match l with
        | [A; x; y] =>
          A' <- fullquote A ;;
          x' <- fullquote x ;;
          y' <- fullquote y ;;
          ret (wEq A' x' y')
        | [A; x] =>
          A' <- fullquote A ;;
          x' <- fullquote x ;;
          ret (wLambda nAnon A' (wEq (↑ A') (↑ x') (wRel 0)))
        | [A] =>
          A' <- fullquote A ;;
          ret (wLambda nAnon A' (wLambda nAnon (↑ A')
                                         (wEq (↑ (↑ A')) (wRel 0) (wRel 1))))
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.eq_refl" then
        match l with
        | [A; x] =>
          A' <- fullquote A ;;
          x' <- fullquote x ;;
          ret (wRefl A' x')
        | [A] =>
          A' <- fullquote A ;;
          ret (wLambda nAnon A' (wRefl (↑ A') (wRel 0)))
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.J" then
        match l with
        | A :: u :: tLambda _ _ (tLambda _ _ P) :: v :: p :: t :: l' =>
          A' <- fullquote A ;;
          u' <- fullquote u ;;
          P' <- fullquote P ;;
          v' <- fullquote v ;;
          p' <- fullquote p ;;
          t' <- fullquote t ;;
          l' <- monad_map fullquote l' ;;
          ret (mkApps (wJ A' u' P' t' v' p') l')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.Jβ" then
        match l with
        | [A; u; tLambda _ _ (tLambda _ _ P); t] =>
          A' <- fullquote A ;;
          u' <- fullquote u ;;
          P' <- fullquote P ;;
          t' <- fullquote t ;;
          (* ret (wJBeta A' u' P' t' v' p' l') *)
          ret (wRel 999)
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.coe" then
        match l with
        | [A; B; e; x] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          e' <- fullquote e ;;
          x' <- fullquote x ;;
          ret (wTransport A' B' e' x')
        | _ => raise (InstanciationNotHandeled c l)
        end

      (* β ? *)

      else if eq_string c "Translation.Quotes.K" then
        match l with
        | [A; u; p] =>
          A' <- fullquote A ;;
          u' <- fullquote u ;;
          p' <- fullquote p ;;
          ret (wK A' u' p')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.funext" then
        match l with
        | [A; B; f; g; e] =>
          f' <- fullquote f ;;
          g' <- fullquote g ;;
          e' <- fullquote e ;;
          ret (wFunext f' g' e')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.heq" then
        match l with
        | [A; a; B; b] =>
          A' <- fullquote A ;;
          a' <- fullquote a ;;
          B' <- fullquote B ;;
          b' <- fullquote b ;;
          ret (wHeq A' a' B' b')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.Pack" then
        match l with
        | [A; B] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          ret (wPack A' B')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.pack" then
        match l with
        | [A; B; u; v; p] =>
          A' <- fullquote A ;;
          B' <- fullquote B ;;
          u' <- fullquote u ;;
          v' <- fullquote v ;;
          p' <- fullquote p ;;
          ret (wpack u' v' p')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.ProjT1" then
        match l with
        | [A; B; u] =>
          u' <- fullquote u ;;
          ret (wProjT1 u')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.ProjT2" then
        match l with
        | [A; B; u] =>
          u' <- fullquote u ;;
          ret (wProjT2 u')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else if eq_string c "Translation.Quotes.ProjTe" then
        match l with
        | [A; B; u] =>
          u' <- fullquote u ;;
          ret (wProjTe u')
        | _ => raise (InstanciationNotHandeled c l)
        end

      else match assoc_at c constt with
      | Some t =>
        l' <- monad_map fullquote l ;;
        ret (mkApps t l')
      | None => raise (UnknownConst c)
      end

    | tApp u [] =>
      fullquote u
    | tApp u [ v ] =>
        u' <- fullquote u ;;
        v' <- fullquote v ;;
        ret (wApp u' v')
    | tApp u (v :: l) =>
      fullquote (tApp (tApp u [ v ]) l)
    | _ => raise (NotHandled t)
  end.

Set Guard Checking.
End fq.


(* Quote Recursively Definition qq := cong_prod. *)

(* Definition qheq := *)
(*   Eval compute in *)
(*   match Typing.lookup_env (Datatypes.fst qq) "Translation.Quotes.heq" with *)
(*   | Some (ConstantDecl _ d) => match d.(cst_body) with *)
(*                               | Some t => t *)
(*                               | None => tRel 87 *)
(*                               end *)
(*   | _ => tRel 90 *)
(*   end. *)

(* Definition sHeq0 := *)
(*   Eval compute in *)
(*   match fullquote empty [pvar 0; pvar 0] qheq with *)
(*   | Success t => t *)
(*   | Error e => wRel 212 *)
(*   end. *)

(* Definition sHeq0_type := *)
(*   Eval compute in *)
(*   match wttinfer [] [] sHeq0 with *)
(*   | Some t => t *)
(*   | None => wRel 48 *)
(*   end. *)

(* Definition type_sHeq0 := *)
(*   wttinfer_sound [] [] sHeq0 sHeq0_type Logic.eq_refl type_glob_nil *)
(*                  (wf_nil _). *)

(* Definition sHeq A a B b s *)
(*   := mkApps (instantiate_sorts (fun _ => s) sHeq0) [A; a; B; b]. *)

Require Import Template.All.
Definition get_level (T : Type) : TemplateMonad string := t <- tmQuote T ;;
                     match t with
                     | tSort [(Level.Level l, false)%core] => tmReturn l
                     | _ => tmFail "blabla"
                     end.

Fixpoint list_to_assoc {A} (l : list (string * A)) : assoc A :=
  match l with
  | [] => empty
  | (s, t) :: l => acons s t (list_to_assoc l)
  end  .

Section l.
Universes i i1 i2 j j1 j2 ij ij1 ij2.

Quote Definition qcong_prod
  := Eval compute in cong_prod@{i i1 i2 j j1 j2 ij ij1 ij2}.

Run TemplateProgram (i <- get_level Type@{i} ;;
                     i1 <- get_level Type@{i1} ;;
                     i2 <- get_level Type@{i2} ;;
                     j <- get_level Type@{j} ;;
                     j1 <- get_level Type@{j1} ;;
                     j2 <- get_level Type@{j2} ;;
                     ij <- get_level Type@{ij} ;;
                     ij1 <- get_level Type@{ij1} ;;
                     ij2 <- get_level Type@{ij2} ;;
                     let l := [(i, pvar 0); (i1, psucc (pvar 0)); (i2, psucc (psucc (pvar 0)));
                               (j, pvar 1); (j1, psucc (pvar 1)); (j2, psucc (psucc (pvar 1)));
                               (ij, pprod_sort (pvar 0) (pvar 1)); (ij1, psucc (pprod_sort (pvar 0) (pvar 1))); (ij2, psucc (psucc (pprod_sort (pvar 0) (pvar 1))))] in
                     l <- tmEval all (list_to_assoc l) ;;
                     tmDefinition "univs" l).

Eval vm_compute in (fullquote empty univs qcong_prod).
Eval vm_compute in (match fullquote empty univs qcong_prod with
             | Error (InstanciationNotHandeled c l) => length l
             | _ => 122
             end).

(* Eval compute in (List.length ()) *)


(* Definition wcong_prod := *)
(*   Eval hnf in *)
(*   fullquote empty univs qcong_prod. with *)
(*   | Success t => t *)
(*   | Error e => wRel 212 *)
(*   end. *)

(* Definition sHeq0_type := *)
(*   Eval compute in *)
(*   match wttinfer [] [] sHeq0 with *)
(*   | Some t => t *)
(*   | None => wRel 48 *)
(*   end. *)

(* Definition type_sHeq0 := *)
(*   wttinfer_sound [] [] sHeq0 sHeq0_type Logic.eq_refl type_glob_nil *)
(*                  (wf_nil _). *)

(* Definition sHeq A a B b s *)
(*   := mkApps (instantiate_sorts (fun _ => s) sHeq0) [A; a; B; b]. *)





Section SS.

Existing Instance nat_sorts.

Section F.
Context `{Sort_notion : Sorts.notion}.

(* freshness ... *)
Definition weak_glob_type' {Σ Γ t A} (h : [] ;;; Γ |-w t : A) :
  Σ ;;; Γ |-w t : A.
Admitted.

(* Fixpoint type_lift' {Σ Γ t A} (h : Σ ;;; [] |-w t : A) : *)
(*   type_glob Σ -> *)
(*   wf Σ Γ -> *)
(*   Σ ;;; Γ |-w lift #|Γ| 0 t : lift #|Γ| 0 A. *)
(* Proof. *)
(*   pose (@type_lift _ Σ [] Γ [] _ _ h). *)
(*   cbn in t0. rewrite nil_cat in t0. *)
(*   assumption. *)
(* Defined. *)
End F.

(* sHeq as s as additional annotation *)
(* Definition type_Heq Σ Γ A a B b s : *)
(*     Σ ;;; Γ |-w A : wSort s -> *)
(*     Σ ;;; Γ |-w B : wSort s -> *)
(*     Σ ;;; Γ |-w a : A -> *)
(*     Σ ;;; Γ |-w b : B -> *)
(*     Σ ;;; Γ |-w sHeq A a B b s : wSort s. *)
(* Proof. *)
(*   intros HA HB Ha Hb. *)
(*   pose proof (instantiate_sorts_sound _ _ (fun _ => s) sHeq0 sHeq0_type type_sHeq0 *)
(*                                       type_glob_nil (wf_nil _)). *)
(*   repeat (eapply meta_conv; [eapply type_App|]). *)
(*   eapply (weak_glob_type' (Σ:=Σ)) in H. *)
(*   refine (type_lift' (Γ:=Γ) H _ _). *)
(*   admit. admit. all: try eassumption. *)
(*   simpl; rewrite lift00; try reflexivity. *)
(*   reflexivity. *)
(*   simpl; rewrite lift00; reflexivity. *)
(*   simpl. *)
(* Abort. *)



(* Compute (List.map global_decl_ident (Datatypes.fst qq)). *)
(* ["Translation.Quotes.sigT"; "Translation.Quotes.eq"; *)
(*  "Translation.Quotes.eq_refl"; "Translation.Quotes.J"; *)
(*  "Translation.Quotes.transport"; "Translation.Quotes.coe"; *)
(*  "Translation.Quotes.heq"; "Translation.Quotes.Pack"; *)
(*  "Translation.Quotes.projT1"; "Translation.Quotes.ProjT1"; *)
(*  "Translation.Quotes.projT2"; "Translation.Quotes.ProjT2"; *)
(*  "Translation.Quotes.existT"; "Translation.Quotes.concat"; *)
(*  "Translation.Quotes.Jβ"; "Translation.Quotes.transportβ"; *)
(*  "Translation.Quotes.coeβ"; "Translation.Quotes.sigT_rec"; *)
(*  "Translation.Quotes.inverse"; "Translation.Quotes.K"; *)
(*  "Translation.Quotes.coeβ'"; "Translation.Quotes.funext"; *)
(*  "Translation.Quotes.heq_to_eq"; "Translation.Quotes.pack"; *)
(*  "Translation.Quotes.heq_refl"; "Translation.Quotes.ap"; *)
(*  "Translation.Quotes.projT1β"; "Translation.Quotes.ProjT1β"; *)
(*  "Translation.Quotes.Ση"; "Translation.Quotes.transport_sigma_const"; *)
(*  "Translation.Quotes.projT2β"; "Translation.Quotes.ProjT2β"; *)
(*  "Translation.Quotes.cong_prod"] *)


Definition T0 := acons "Translation.Quotes.sigT" (wSum) empty.

End SS.

End l.