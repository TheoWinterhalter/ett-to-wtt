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

(* TODO Move in ExamplesUtil *)
Fixpoint Prods (Γ : scontext) (T : sterm) :=
  match Γ with
  | A :: Γ => Prods Γ (sProd nAnon A T)
  | [] => T
  end.

Lemma lift_rel :
  forall {t k}, (lift 1 (S k) t) {k := sRel 0} = t.
Proof.
  intro t. induction t ; intro k.
  all: try (cbn ; f_equal ; easy).
  destruct n.
  - cbn. case_eq (k ?= 0) ; intro e ; bprop e.
    + subst. reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn. case_eq (k <=? n) ; intro e ; bprop e.
    + cbn. case_eq (k ?= S (S n)) ; intro e1 ; bprop e1 ; try myomega.
      reflexivity.
    + cbn. case_eq (k ?= S n) ; intro e1 ; bprop e1 ; try myomega.
      * subst. f_equal. myomega.
      * reflexivity.
Defined.

Lemma close_goal_ex :
  forall {Σ Γ t T},
    xtype_glob Σ ->
    Σ ;;; [] |-x t : Prods Γ T ->
    Σ ;;; Γ |-x T : Ty ->
    ∑ t', Σ ;;; Γ |-x t' : T.
Proof.
  intros Σ Γ t T hg h hT.
  revert t T h hT. induction Γ as [| A Γ].
  - intros t T h hT. eexists. eassumption.
  - intros t T h hT. cbn in h.
    destruct (IHΓ _ _ h) as [t' ht'].
    + pose proof (typing_wf hT) as hw.
      inversion hw. subst. destruct s.
      eapply xtype_Prod'.
      * eassumption.
      * intros _. eassumption.
    + eexists. eapply meta_conv.
      * eapply xtype_App'.
        -- assumption.
        -- instantiate (2 := lift0 1 A).
           instantiate (1 := lift 1 1 T).
           instantiate (1 := nAnon).
           change (sProd nAnon (lift0 1 A) (lift 1 1 T))
             with (lift0 1 (sProd nAnon A T)).
           eapply typing_lift01.
           ++ assumption.
           ++ exact ht'.
           ++ instantiate (1 := tt).
              pose proof (typing_wf hT) as hw.
              inversion hw. subst. destruct s.
              assumption.
        -- instantiate (1 := sRel 0). ettcheck  Σi.
           pose proof (typing_wf hT) as hw.
           inversion hw. subst. destruct s.
           assumption.
      * eapply lift_rel.
Defined.

Lemma inversionProds :
  forall {Σ Γ T},
    Σ ;;; [] |-x Prods Γ T : Ty ->
    (Σ ;;; Γ |-x T : Ty).
Proof.
  intros Σ Γ T h. revert T h.
  induction Γ as [| A Γ] ; intros T h.
  - cbn in h. assumption.
  - cbn in h.
    specialize (IHΓ _ h).
    destruct (XInversions.inversionProd IHΓ) as [[? ?] ?].
    assumption.
Defined.

Lemma close_goal_ex' :
  forall {Σ Γ t T},
    xtype_glob Σ ->
    Σ ;;; [] |-x t : Prods Γ T ->
    ∑ t', Σ ;;; Γ |-x t' : T.
Proof.
  intros Σ Γ t T hg ht.
  eapply close_goal_ex ; try eassumption.
  destruct (istype_type hg ht) as [[] hT].
  eapply inversionProds. assumption.
Defined.

Definition closet {Σ Γ t T} hg h :=
  let '(t' ; _) := @close_goal_ex' Σ Γ t T hg h in t'.

Definition close_goal :
  forall {Σ Γ t T}
    (hg : xtype_glob Σ)
    (h : Σ ;;; [] |-x t : Prods Γ T),
    Σ ;;; Γ |-x closet hg h : T.
Proof.
  intros Σ Γ t T h.
  eapply close_goal_ex'.
Defined.

Transparent Σi.

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

Definition type_vrev_ := Eval lazy - [Σi] in type_vrev.

Print type_vrev_.

Definition itt_vrev : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_vrev_ istrans_nil in t.

Print itt_vrev.

Definition tc_vrev : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] itt_vrev empty.

Print tc_vrev.

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