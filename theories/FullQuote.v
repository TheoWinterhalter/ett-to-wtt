(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template
Require Import Ast utils monad_utils Typing Checker.
From Translation
Require Import util Sorts WAst WLiftSubst WTyping WChecker WLemmata Quotes.
From TypingFlags Require Import Loader.
Import MonadNotation ListNotations.

Axiom myadmit : forall {A}, A.

Inductive fq_error {S : notion} :=
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
| InferenceFailed (id : string) (e : i_error)
.

Definition fq_result {S : notion} := result fq_error.

Local Existing Instance psort_notion.
(* Definition tsl_univ (univs : assoc sort) (u : universe) := *)
(*   match u with *)
(*   | [ pair (Level.Level l) (false) ] => *)
(*     match assoc_at l univs with *)
(*     | Some t => Success t *)
(*     | None  => Error NotEnoughSorts *)
(*     end *)
(*   | _ => Error AlgebraicUniverse *)
(*   end. *)
Definition tsl_univ (univs : list sort) (u : universe) :=
  match u with
  | [ pair (Level.Var n) (false) ] =>
    match nth_error univs n with
    | Some t => Success t
    | None  => Error NotEnoughSorts
    end
  | _ => Error AlgebraicUniverse
  end.


Section fq.
Unset Guard Checking.

Context (constt : assoc wterm) (univs : list sort).

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
          u' <- fullquote u ;;
          P' <- fullquote P ;;
          t' <- fullquote t ;;
          ret (wJBeta u' P' t')
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



Quote Recursively Definition all_constants :=
  (cong_prod, cong_lambda, cong_app, cong_sum, cong_pi1, cong_pi2,
   cong_eq, cong_refl).

Fixpoint keep_unknown_constants gdecls :=
  match gdecls with
  | [] => empty
  | (ConstantDecl kn {| cst_body := Some t; cst_type := A |}) :: gdecls
    => acons kn (t , A) (keep_unknown_constants gdecls)
  | _ :: gdecls => keep_unknown_constants gdecls
  end.

Definition unknown_constants :=
  keep_unknown_constants (Datatypes.fst all_constants).


Definition tsl_constant TC univs c :=
  let body :=
      match assoc_at c unknown_constants with
      | Some (t , _) => t
      | _ => tRel 90
      end in
  let bodyᵗ :=
      match fullquote TC univs body with
      | Success t => t
      | Error e => wRel 212
      end in
  acons c bodyᵗ TC.

Fixpoint keys {A} (l : assoc A) :=
  match l with
  | empty => []
  | acons key data t => key :: (keys t)
  end.

Eval compute in (keys unknown_constants).


Definition TC :=
  (* Eval compute in *)
  (let TC := empty in                 
  let TC := tsl_constant TC [pvar 0; pvar 1] "Translation.Quotes.transport" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.coe" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.heq" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.Pack" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.ProjT1" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.ProjT2" in
  let TC := tsl_constant TC [pvar 0] "Translation.Quotes.concat" in
  let TC := tsl_constant TC [pvar 0; pvar 1] "Translation.Quotes.transportβ" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.coeβ" in
  let TC := tsl_constant TC [pvar 0] "Translation.Quotes.inverse" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.coeβ'" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.heq_to_eq" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.pack" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.heq_refl" in
  let TC := tsl_constant TC [pvar 0; pvar 1] "Translation.Quotes.ap" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.ProjT1β" in
  let TC := tsl_constant TC [pvar 0; pvar 1; psum_sort (pvar 0) (pvar 1)] "Translation.Quotes.transport_sigma_const" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.ProjT2β" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0); pvar 1; psucc (pvar 1); psucc (psucc (pvar 1)); psucc (pprod_sort (pvar 0) (pvar 1))] "Translation.Quotes.heq_to_eq_fam" in
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_prod" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.eq_to_heq" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.sigT_rec" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.heq_trans" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.heq_apD" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_lambda" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_app" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_sum" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_pi1" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_pi2" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_eq" in *)
  (* let TC := tsl_constant TC [pvar 0] "Translation.Quotes.cong_refl" in *)
  TC).


Definition tsl_constant' TC univs c :=
  let typ :=
      match assoc_at c unknown_constants with
      | Some (t , A) => A
      | _ => tRel 90
      end in
  match fullquote TC univs typ with
  | Success t => t
  | Error e => wRel 212
  end.

Eval lazy in (assoc_at "Translation.Quotes.transport" TC).

Definition wtransport := (wLambda (nNamed "A") (wSort (pvar 0))
            (wLambda (nNamed "P") (wProd nAnon (wRel 0) (wSort (pvar 1)))
               (wLambda (nNamed "x") (wRel 1)
                  (wLambda (nNamed "y") (wRel 2)
                     (wLambda (nNamed "p") (wEq (wRel 3) (wRel 1) (wRel 0))
                        (wLambda (nNamed "u") (wApp (wRel 3) (wRel 2))
                           (wJ (wRel 5) (wRel 3) (wApp (wRel 6) (wRel 1)) 
                              (wRel 0) (wRel 2) (wRel 1)))))))).

Eval lazy in (tsl_constant' TC [pvar 0; pvar 1] "Translation.Quotes.transport").

Definition wtransport_type := wProd (nNamed "A") (wSort (pvar 0))
         (wProd (nNamed "P") (wProd nAnon (wRel 0) (wSort (pvar 1)))
            (wProd (nNamed "x") (wRel 1)
               (wProd (nNamed "y") (wRel 2)
                  (wProd (nNamed "p") (wEq (wRel 3) (wRel 1) (wRel 0))
                     (wProd (nNamed "u") (wApp (wRel 3) (wRel 2))
                        (wApp (wRel 4) (wRel 2))))))).

(* Lemma heq_sort {Σ} : Σ ;;; [] |-w wtransport : wtransport_type. *)



(* Eval hnf in (assoc_at "Translation.Quotes.heq_to_eq_fam" TC). *)

(* Definition infer_type_cst (Σ : wglobal_context) TC cst := *)
(*   match assoc_at cst TC with *)
(*   | Some t  =>  *)
(*     match wttinfer Σ [] t with *)
(*     | Some t => t *)
(*     | None => wRel 48 *)
(*     end *)
(*   | None => wRel 77 *)
(*   end. *)

(* Program Definition try_enrich_Σ (Σ : wglobal_context) (wΣ : type_glob Σ) TC cst *)
(*   : {Σ' & type_glob Σ'} := *)
(*   match assoc_at cst TC with *)
(*   | Some t  =>  *)
(*     match wttinfer Σ [] t with *)
(*     | Some typ => Specif.existT _ (Build_glob_decl cst typ :: Σ) _ *)
(*     | None => Specif.existT _ Σ wΣ *)
(*     end *)
(*   | None => Specif.existT _ Σ wΣ *)
(*   end. *)
(* Next Obligation. *)
(*   simple refine (let X := wttinfer_sound Σ [] t typ _ wΣ *)
(*                  (wf_nil _) in _). *)
(*   now symmetry. *)
(*   econstructor. assumption. apply myadmit. *)
(*   eapply istype_type; eassumption. *)
(* Defined. *)

Notation "'exists' x .. y , p" := (pp_sigT (fun x => .. (pp_sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Program Definition try_tsl_cst (Σ : wglobal_context) (wΣ : type_glob Σ)
                       (TC : assoc wterm) (cst : string)
  : fq_result ((exists t A, Σ ;;; [] |-w t : A) * (exists Σ', type_glob Σ')) :=
  match assoc_at cst TC with
  | Some t  => 
    match wttinfer Σ [] t with
    | Success typ => Success (( t ; typ ; _) , (Build_glob_decl cst typ t :: Σ; _))
    | Error e => Error (InferenceFailed cst e)
    end
  | None => Error (MsgError (cst ++ " not found in the tsl ctx"))
  end.
Next Obligation.
  simple refine (wttinfer_sound Σ [] t typ _ wΣ (wf_nil _)).
  now symmetry.
Defined.
Next Obligation.
  simple refine (let X := wttinfer_sound Σ [] t typ _ wΣ
                 (wf_nil _) in _).
  now symmetry.
  econstructor. assumption. apply myadmit.
  cbn. eassumption.
Defined.

Fixpoint TC_to_Σ (Σ : wglobal_context) (TC : assoc wterm) : wglobal_context :=
  match TC with
  | empty => Σ
  | acons cst t TC =>
    let Σ' := TC_to_Σ Σ TC in
    match wttinfer Σ' [] t with
    | Success typ => Build_glob_decl cst typ t :: Σ'
    | Error _ => Σ'
    end
  end.

(* Eval lazy in (TC_to_Σ [] TC). *)

Definition wcoe :=
  Eval lazy in (assoc_at "Translation.Quotes.coe" TC).
Set Printing Universes.
Eval compute in ((assoc_at "Translation.Quotes.coe" unknown_constants)).
Eval lazy in (fullquote TC [pvar 12; pvar 13] (tLambda (nNamed "A") (tSort [(Level.Var 1, false)%core])
            (tLambda (nNamed "B") (tSort [(Level.Var 0, false)%core])
               (tLambda (nNamed "p")
                  (tApp (tConst "Translation.Quotes.eq" [Level.Var 1])
                     [tSort [(Level.Var 0, false)%core]; tRel 1; tRel 0])
                  (tLambda (nNamed "x") (tRel 2)
                     (tApp
                        (tConst "Translation.Quotes.transport"
                           [Level.Var 1; Level.Var 0])
                        [tSort [(Level.Var 0, false)%core];
                        tLambda (nNamed "T") (tSort [(Level.Var 0, false)%core])
                          (tRel 0); tRel 3; tRel 2; tRel 1; 
                        tRel 0])))))).
Eval unfold coe, transport in @coe.
Definition wcoe_type :=
  Eval lazy in
  match wcoe with
  | Some t  => wttinfer (TC_to_Σ [] TC) [] t
  | None => raise (Msg "you made a mistake!")
  end.


Eval compute in
    (try_tsl_cst [] type_glob_nil TC "Translation.Quotes.transport").

  let TC := tsl_constant TC [pvar 0; pvar 1] "Translation.Quotes.transport" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.coe" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.heq" in
  let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.Pack" in

Definition sHeq0_type :=
  Eval compute in
  match assoc_at "Translation.Quotes.heq_to_eq_fam" TC with
  | Some t  => 
    match wttinfer [] [] t with
    | Some t => t
    | None => wRel 48
    end.

Definition type_sHeq0 :=
  wttinfer_sound [] [] sHeq0 sHeq0_type Logic.eq_refl type_glob_nil
                 (wf_nil _).

Definition sHeq A a B b s
  := mkApps (instantiate_sorts (fun _ => s) sHeq0) [A; a; B; b].

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