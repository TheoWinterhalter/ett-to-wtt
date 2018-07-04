Require Import TypingFlags.Loader.
Set Type In Type.

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
  Eval lazy in fullquote (2 ^ 18) Σ [] vrev_term indt constt cot.
Definition tm_vrev :=
  Eval lazy in 
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
  ettcheck.
  - instantiate (1 := nNamed "m").
    eapply reflection.
    instantiate (1 := sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation1") _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)).
    ettcheck.
    Opaque Σi.
    all: lazy.
    all: try eapply eq_reflexivity.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + lazy. ettcheck.
    + ettcheck.
    + lazy. ettcheck.
    + ettcheck.
    + lazy. ettcheck.
    + ettcheck.
    + lazy. ettcheck.
    + ettcheck.
    + lazy. ettcheck.
    + ettcheck.
    + lazy. ettcheck.
    + ettcheck.
  - Opaque Σi. lazy. eapply reflection.
    instantiate (2 := sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation2") _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)).
    ettcheck.
    all: lazy.
    all: try eapply eq_reflexivity.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
  - Opaque Σi. lazy. eapply reflection.
    instantiate (1 := sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation3") _ _ (sRel 10)) _ _ (sRel 9)) _ _ (sRel 8)) _ _ (sRel 7)) _ _ (sRel 6)) _ _ (sRel 5)) _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)).
    ettcheck.
    all: lazy.
    all: try eapply eq_reflexivity.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
  - Opaque Σi. lazy. eapply reflection.
    instantiate (2 := sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation2") _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)).
    ettcheck.
    all: lazy.
    all: try eapply eq_reflexivity.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck.
    + ettcheck. lazy. ettcheck.
Defined.
(* TODO Maybe prove something about closure like:
   to have e such that Γ |- e : T,
   it is enough to have e' such that |- e' : ∀ Γ, T.
   That way, we can use the obligations directly.
 *)

(* Definition itt_vrev : sterm := *)
(*   Eval lazy in *)
(*   let '(_ ; t ; _) := type_translation type_vrev istrans_nil in t. *)

(* Definition tc_vrev : tsl_result term := *)
(*   Eval lazy in *)
(*   tsl_rec (2 ^ 18) Σ [] itt_vrev empty. *)

(* Make Definition coq_vrev := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_vrev with *)
(*               | FinalTranslation.Success _ t => t *)
(*               | _ => tRel 0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)