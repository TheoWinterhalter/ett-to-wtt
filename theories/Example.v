(* -*- coq-prog-args: ("-emacs" "-type-in-type") -*- *)

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker.
From Translation Require Import util Sorts SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Quotes Translation FinalTranslation
                                FullQuote ExamplesUtil ExampleQuotes.

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
  ettcheck. cbn.
  eapply reflection with (e := sRel 1).
  ettcheck.
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
  ettcheck.
Defined.

Definition itt_realid : sterm :=
  Eval lazy in
  let '(_ ; t ; _) := type_translation type_realid istrans_nil in t.

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

Fail Definition vrev0 {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m)) 
           (fun m acc => acc) (fun a n _ rv m acc => rv _ (vcons a m acc))
           n v m acc.

Definition vrev0 {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m)) 
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

Quote Definition vrev0_term :=
  ltac:(let t := eval unfold vrev0 in @vrev0 in exact t).
Quote Definition vrev0_type := 
  ltac:(let T := type of @vrev0 in exact T).

Definition pretm_vrev0 :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vrev0_term indt constt cot.
Definition tm_vrev0 :=
  Eval lazy in 
  match pretm_vrev0 with
  | Success t => t
  | Error _ => sRel 0
  end.

Definition prety_vrev0 :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vrev0_type indt constt cot.
Definition ty_vrev0 :=
  Eval lazy in 
  match prety_vrev0 with
  | Success t => t
  | Error _ => sRel 0
  end.

Lemma type_vrev0 : Σi ;;; [] |-x tm_vrev0 : ty_vrev0.
Proof.
  unfold tm_vrev0, ty_vrev0.
  ettcheck.
  - Opaque Σi.
    assert (xmeta_eq_conv : forall {Σ Γ u v A B}, Σ ;;; Γ |-x u = v : A -> A = B -> Σ ;;; Γ |-x u = v : B).
    { clear. intros Σ Γ u v A B h e. destruct e. assumption. }
    eapply eq_symmetry.
    eapply eq_transitivity.
    + eapply xmeta_eq_conv.
      * eapply cong_App.
        -- eapply eq_reflexivity. ettcheck.
        -- eapply eq_reflexivity. ettcheck.
        -- eapply xmeta_eq_conv.
           ++ eapply eq_beta.
              ** ettcheck.
              ** ettcheck.
              ** ettcheck.
              ** ettcheck.
           ++ lazy. reflexivity.
        -- eapply eq_reflexivity. ettcheck.
        -- ettcheck.
        -- ettcheck.
        -- ettcheck.
        -- lazy. ettcheck.
        -- ettcheck.
        -- ettcheck.
      * reflexivity.
    + lazy. eapply eq_transitivity.
      * eapply xmeta_eq_conv.
        -- eapply eq_beta.
           ++ ettcheck.
           ++ ettcheck.
           ++ ettcheck.
           ++ ettcheck.
        -- reflexivity.
      * lazy. eapply xmeta_eq_conv.
        -- eapply cong_Prod.
           ++ apply eq_reflexivity. ettcheck.
           ++ eapply cong_Prod.
              ** apply eq_reflexivity. ettcheck.
              ** eapply xmeta_eq_conv.
                 --- eapply cong_App.
                     +++ apply eq_reflexivity. ettcheck.
                     +++ apply eq_reflexivity. ettcheck.
                     +++ apply eq_reflexivity. ettcheck.
                     +++ (* 0 + x = x *)
                         (* This suggests that we should use reflection at
                            top-level for all conversions.
                            Doing beta-conversions by hand is too cumbersome
                            anyway.
                          *)
Abort.
(*   - lazy. admit. *)
(*   - lazy. eapply reflection with (e := sAx "vrev_eq0"). ettcheck. *)
(*   - lazy. eapply reflection with (e := sAx "vrev_eq1"). ettcheck. *)
(* Defined. *)

(* Definition itt_vrev0 : sterm := *)
(*   Eval lazy in *)
(*   let '(_ ; t ; _) := type_translation type_vrev0 istrans_nil in t. *)

(* Definition tc_vrev0 : tsl_result term := *)
(*   Eval lazy in *)
(*   tsl_rec (2 ^ 18) Σ [] itt_vrev0 empty. *)

(* Make Definition coq_vrev0 := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_vrev0 with *)
(*               | FinalTranslation.Success _ t => t *)
(*               | _ => tRel 0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)