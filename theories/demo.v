Require Import TypingFlags.Loader.
Set Type In Type.

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import All.
From Translation Require Import util Sorts SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Quotes Translation FinalTranslation
                                FullQuote ExampleQuotes ExamplesUtil
                                XTypingLemmata IChecking XChecking.
Import MonadNotation.

Open Scope string_scope.
Open Scope x_scope.

Definition nomap : string -> nat -> option sterm := fun _ _ => None.

Definition Translate ident : TemplateMonad () :=
  entry <- tmQuoteConstant ident false ;;
  match entry with
  | DefinitionEntry {| definition_entry_body := tm ; definition_entry_type := ty |} =>
    pretm <- tmEval lazy (fullquote (2 ^ 18) Σ [] tm indt constt cot) ;;
    prety <- tmEval lazy (fullquote (2 ^ 18) Σ [] ty indt constt cot) ;;
    match pretm, prety with
    | Success tm, Success ty =>
      name <- tmEval all (ident ++ "_der") ;;
      name <- tmFreshName name ;;
      der <- tmLemma name (Σi ;;; [] |-x tm : ty) ;;
      let '(_ ; itt_tm ; _) := type_translation der istrans_nil in
      t <- tmEval lazy (tsl_rec (2 ^ 18) Σ [] itt_tm axoc) ;;
      match t with
      | FinalTranslation.Success _ t =>
        (* t' <- tmUnquote t ;; *)
        (* t' <- tmEval Core.hnf (my_projT2 t') ;; *)
        (* tmPrint t' *)
        tmMkDefinition (ident ++ "ᵗ") t
      | _ => tmFail "Cannot translate from ITT to TemplateCoq"
      end
    | _,_ => tmFail "Cannot transalte from TemplateCoq to ETT"
    end
  | _ => tmFail "Expected a constant definition"
  end.













(*! EXAMPLE 1 *)

Fail Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := x.

Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}.

Quote Definition pseudoid_term :=
  ltac:(let t := eval compute in pseudoid in exact t).
Quote Definition pseudoid_type :=
  ltac:(let T := type of pseudoid in exact T).

Definition pretm_pseudoid :=
  Eval lazy in fullquote (2 ^ 18) Σ [] pseudoid_term empty empty nomap.
Definition tm_pseudoid :=
  Eval lazy in
  match pretm_pseudoid with
  | Success t => t
  | Error _ => sRel 0
  end.

Definition prety_pseudoid :=
  Eval lazy in fullquote (2 ^ 18) Σ [] pseudoid_type empty empty nomap.

Definition ty_pseudoid :=
  Eval lazy in
  match prety_pseudoid with
  | Success t => t
  | Error _ => sRel 0
  end.

Lemma type_pseudoid : Σi ;;; [] |-x tm_pseudoid : ty_pseudoid.
Proof.
  unfold tm_pseudoid, ty_pseudoid.
  pose proof xhΣi.
  ettcheck Σi. cbn.
  eapply reflection with (e := sRel 1).
  ettcheck Σi.
Defined.

Definition itt_pseudoid : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_pseudoid istrans_nil in t.

Definition tc_pseudoid : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_pseudoid empty.

Make Definition coq_pseudoid :=
  ltac:(
    let t := eval lazy in
             (match tc_pseudoid with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).



































(*! EXAMPLE 2 *)

Definition repseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}.

Run TemplateProgram (Translate "repseudoid").
Next Obligation.
  pose proof xhΣi.
  ettcheck Σi. cbn.
  eapply reflection with (e := sRel 1).
  ettcheck Σi.
Defined.

Print repseudoidᵗ.









































(*! EXAMPLE 3 *)

Fail Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => rv _ (vcons a m acc))
           n v m acc.

Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

Arguments vrev : clear implicits.

Run TemplateProgram (Translate "vrev").
Next Obligation.
  pose proof xhΣi.
  (* ettcheck Σi. *)
  (* - eapply reflection. *)
  (*   unshelve eapply close_goal *)
  (*   ; [ exact (sAx "vrev_obligation1") | assumption |]. *)
  (*   simpl. ettcheck Σi. *)
  (* - eapply reflection. *)
  (*   unshelve eapply close_goal *)
  (*   ; [ exact (sAx "vrev_obligation2") | assumption |]. *)
  (*   simpl. ettcheck Σi. *)
  (* - eapply reflection. *)
  (*   unshelve eapply close_goal *)
  (*   ; [ exact (sAx "vrev_obligation3") | assumption |]. *)
  (*   simpl. ettcheck Σi. *)
  (* - eapply reflection. *)
  (*   unshelve eapply close_goal *)
  (*   ; [ exact (sAx "vrev_obligation4") | assumption |]. *)
  (*   simpl. ettcheck Σi. *)
  (* Unshelve. all: exact nAnon. *)
Abort.

Quote Definition vrev_term :=
  ltac:(let t := eval unfold vrev in @vrev in exact t).
Quote Definition vrev_type :=
  ltac:(let T := type of @vrev in exact T).

Definition pretm_vrev :=
  Eval lazy - [Σi] in fullquote (2 ^ 18) Σ [] vrev_term indt constt cot.
Definition tm_vrev :=
  Eval lazy - [Σi] in
  match pretm_vrev with
  | Success t => t
  | Error _ => sRel 0
  end.

Definition prety_vrev :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vrev_type indt constt cot.
Definition ty_vrev :=
  Eval lazy in
  match prety_vrev with
  | Success t => t
  | Error _ => sRel 0
  end.

Lemma type_vrev : Σi ;;; [] |-x tm_vrev : ty_vrev.
Proof.
  unfold tm_vrev, ty_vrev.
  pose proof xhΣi.
  ettcheck Σi.
  - eapply reflection.
    unshelve eapply close_goal
    ; [ exact (sAx "vrev_obligation1") | assumption |].
    simpl. ettcheck Σi.
  - eapply reflection.
    unshelve eapply close_goal
    ; [ exact (sAx "vrev_obligation2") | assumption |].
    simpl. ettcheck Σi.
  - eapply reflection.
    unshelve eapply close_goal
    ; [ exact (sAx "vrev_obligation3") | assumption |].
    simpl. ettcheck Σi.
  - eapply reflection.
    unshelve eapply close_goal
    ; [ exact (sAx "vrev_obligation4") | assumption |].
    simpl. ettcheck Σi.
  Unshelve. all: exact nAnon.
Defined.

Definition itt_vrev : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_vrev istrans_nil in t.

Definition tc_vrev : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_vrev axoc.

Make Definition coq_vrev :=
  ltac:(
    let t := eval lazy in
             (match tc_vrev with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).

Print coq_vrev.