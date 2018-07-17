Require Import TypingFlags.Loader.
Set Type In Type.

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import All.
From Translation Require Import util Sorts SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Quotes Translation FinalTranslation
                                FullQuote ExamplesUtil ExampleQuotes
                                XTypingLemmata IChecking XChecking.
Import MonadNotation.

Open Scope string_scope.
Open Scope x_scope.

Definition nomap : string -> nat -> option sterm := fun _ _ => None.

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

(* Definition Translate ident : TemplateMonad () := *)
(*   entry <- tmQuoteConstant ident false ;; *)
(*   match entry with *)
(*   | DefinitionEntry {| definition_entry_body := tm ; definition_entry_type := ty |} => *)
(*     pretm <- tmEval lazy (fullquote (2 ^ 18) Σ [] tm empty empty nomap) ;; *)
(*     prety <- tmEval lazy (fullquote (2 ^ 18) Σ [] ty empty empty nomap) ;; *)
(*     match pretm, prety with *)
(*     | Success tm, Success ty => *)
(*       name <- tmEval all (ident ++ "_der") ;; *)
(*       name <- tmFreshName name ;; *)
(*       der <- tmLemma name (Σi ;;; [] |-x tm : ty) ;; *)
(*       let '(_ ; itt_tm ; _) := type_translation der istrans_nil in *)
(*       t <- tmEval lazy (tsl_rec (2 ^ 18) Σ [] itt_tm empty) ;; *)
(*       match t with *)
(*       | FinalTranslation.Success _ t => *)
(*         t' <- tmUnquote t ;; *)
(*         t' <- tmEval Ast.hnf (my_projT2 t') ;; *)
(*         tmPrint t' *)
(*       | _ => tmFail "Cannot translate from ITT to TemplateCoq" *)
(*       end *)
(*     | _,_ => tmFail "Cannot transalte from TemplateCoq to ETT" *)
(*     end *)
(*   | _ => tmFail "Expected a constant definition" *)
(*   end. *)

(* Run TemplateProgram (Translate "pseudoid"). *)
(* Next Obligation. *)
(*   pose proof xhΣi. *)
(*   ettcheck. cbn. eapply reflection with (e := sRel 1). ettcheck. *)
(* Defined. *)

(*! EXAMPLE 2 *)

Definition realid := fun (A B : Type) (x : A) => x.
Quote Definition realid_term := 
  ltac:(let t := eval compute in realid in exact t).
Quote Definition realid_type := 
  ltac:(let T := type of realid in exact T).

Definition pretm_realid :=
  Eval lazy in fullquote (2 ^ 18) Σ [] realid_term empty empty nomap.
Definition tm_realid :=
  Eval lazy in 
  match pretm_realid with
  | Success t => t
  | Error _ => sRel 0
  end.

Definition prety_realid :=
  Eval lazy in fullquote (2 ^ 18) Σ [] realid_type empty empty nomap.
Definition ty_realid :=
  Eval lazy in 
  match prety_realid with
  | Success t => t
  | Error _ => sRel 0
  end.

Lemma type_realid : Σi ;;; [] |-x tm_realid : ty_realid.
Proof.
  unfold tm_realid, ty_realid.
  pose proof xhΣi.
  ettcheck Σi.
Defined.

Definition type_realid_ := Eval lazy - [Σi] in type_realid.

Definition itt_realid : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_realid_ istrans_nil in t.

Definition tc_realid : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_realid empty.

Make Definition coq_realid :=
  ltac:(
    let t := eval lazy in
             (match tc_realid with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).

(*! EXAMPLE 3 *)

Definition vv : vec nat 1 := vcons 2 _ vnil.

Quote Definition vv_term :=
  ltac:(let t := eval unfold vv in @vv in exact t).
Quote Definition vv_type := 
  ltac:(let T := type of @vv in exact T).

Definition pretm_vv :=
  Eval lazy - [Σi] in fullquote (2 ^ 18) Σ [] vv_term indt constt cot.
Definition tm_vv :=
  Eval lazy - [Σi] in 
  match pretm_vv with
  | Success t => t
  | Error _ => sRel 0
  end.

Definition prety_vv :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vv_type indt constt cot.
Definition ty_vv :=
  Eval lazy in 
  match prety_vv with
  | Success t => t
  | Error _ => sRel 0
  end.

Lemma type_vv : Σi ;;; [] |-x tm_vv : ty_vv.
Proof.
  unfold tm_vv, ty_vv.
  pose proof xhΣi.
  ettcheck Σi.
Defined.

Definition itt_vv : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_vv istrans_nil in t.

Definition tc_vv : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_vv axoc.

Make Definition coq_vv :=
  ltac:(
    let t := eval lazy in
             (match tc_vv with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).


(*! EXAMPLE 4 *)

Fail Definition vcons_act {A n X} (f : vec A (n + 1) -> X) (a : A) (v : vec A n) : X
  := f (vcons a n v).

Definition vcons_act {A n X} (f : vec A (n + 1) -> X) (a : A) (v : vec A n) : X
  := f {! vcons a n v !}.

Quote Definition vcons_act_term :=
  ltac:(let t := eval unfold vcons_act in @vcons_act in exact t).
Quote Definition vcons_act_type := 
  ltac:(let T := type of @vcons_act in exact T).

Definition pretm_vcons_act :=
  Eval lazy - [Σi] in fullquote (2 ^ 18) Σ [] vcons_act_term indt constt cot.
Definition tm_vcons_act :=
  Eval lazy - [Σi] in 
  match pretm_vcons_act with
  | Success t => t
  | Error _ => sRel 0
  end.

Definition prety_vcons_act :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vcons_act_type indt constt cot.
Definition ty_vcons_act :=
  Eval lazy in 
  match prety_vcons_act with
  | Success t => t
  | Error _ => sRel 0
  end.

Lemma type_vcons_act : Σi ;;; [] |-x tm_vcons_act : ty_vcons_act.
Proof.
  unfold tm_vcons_act, ty_vcons_act.
  pose proof xhΣi.
  ettcheck Σi.
  eapply reflection.
  unshelve eapply close_goal
  ; [ exact (sAx "vcons_act_obligation") | assumption |].
  simpl. ettcheck Σi.
Defined.

Definition itt_vcons_act : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_vcons_act istrans_nil in t.

Definition tc_vcons_act : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_vcons_act axoc.

Fail Make Definition coq_vcons_act :=
  ltac:(
    let t := eval lazy in
             (match tc_vcons_act with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).

(*! EXAMPLE 5 *)

Fail Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => rv _ (vcons a m acc))
           n v m acc.

Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

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
  Unshelve. exact nAnon.
Defined.

Definition itt_vrev : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_vrev istrans_nil in t.

Print itt_vrev.

Definition tc_vrev : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_vrev axoc.

Print tc_vrev.

Fail Make Definition coq_vrev :=
  ltac:(
    let t := eval lazy in
             (match tc_vrev with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).

Print coq_vrev.