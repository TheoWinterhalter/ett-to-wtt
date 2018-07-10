(*! Global context and utility for examples *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import utils Ast LiftSubst Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible XTyping
     FundamentalLemma Translation FinalTranslation FullQuote ExampleQuotes
     XTypingLemmata IChecking XChecking.

(* The context for Template Coq *)

(* We define a term that mentions everything that the global context should
   have. *)
Definition glob_term :=
  let _ := @pp_sigT in
  let _ := @epair in
  let _ := @pi1 in
  let _ := @pi2 in
  let _ := @eq in
  let _ := @transport in
  let _ := @K in
  let _ := @funext in
  let _ := @heq in
  let _ := @heq_to_eq in
  let _ := @heq_refl in
  let _ := @heq_sym in
  let _ := @heq_trans in
  let _ := @heq_transport in
  let _ := @Pack in
  let _ := @ProjT1 in
  let _ := @ProjT2 in
  let _ := @ProjTe in
  let _ := @cong_prod in
  let _ := @cong_app in
  let _ := @cong_lambda in
  let _ := @cong_sum in
  let _ := @cong_pair in
  let _ := @cong_pi1 in
  let _ := @cong_pi2 in
  let _ := @cong_eq in
  let _ := @cong_refl in
  let _ := @eq_to_heq in
  let _ := @heq_type_eq in
  (* Candidate *)
  let _ := @candidate in
  (* For examples *)
  let _ := nat in
  let _ := vec in
  let _ := vec_rect in
  let _ := Nat.add in
  let _ := vrev_obligation1 in
  let _ := vrev_obligation2 in
  let _ := vrev_obligation3 in
  let _ := vrev_obligation4 in
  Type.

Quote Recursively Definition glob_prog := @glob_term.
Definition Σ : global_context :=
  (* Eval lazy in *)
  (* reconstruct_global_context (Datatypes.fst glob_prog). *)
  pair (Datatypes.fst glob_prog) init_graph.

Arguments Σ : simpl never.

Definition decl := Build_glob_decl.

Open Scope string_scope.
Open Scope s_scope.

Module IT := ITyping.
Module IL := ITypingLemmata.

(* Preparing the global context (axioms) for examples *)

Definition indt :=
  [< "Coq.Init.Datatypes.nat" --> sAx "nat" ;
     "Translation.ExampleQuotes.vec" --> sAx "vec"
  >].

Definition constt :=
  [< "Coq.Init.Nat.add" --> sAx "add" ;
     "Translation.ExampleQuotes.vec_rect" --> sAx "vec_rect"
  >].

Definition cot (id : string) (n : nat) : option sterm :=
  match id, n with
  | "Coq.Init.Datatypes.nat", 0 => Some (sAx "O")
  | "Coq.Init.Datatypes.nat", 1 => Some (sAx "S")
  | "Translation.ExampleQuotes.vec", 0 => Some (sAx "vnil")
  | "Translation.ExampleQuotes.vec", 1 => Some (sAx "vcons")
  | _,_ => None
  end.

(* nat *)
Quote Definition nat_type := 
  ltac:(let T := type of nat in exact T).
Definition prety_nat :=
  Eval lazy in fullquote (2 ^ 18) Σ [] nat_type indt constt cot.
Definition ty_nat :=
  Eval lazy in 
  match prety_nat with
  | Success t => t
  | Error _ => sRel 0
  end.

(* O *)
Quote Definition O_type := 
  ltac:(let T := type of O in exact T).
Definition prety_O :=
  Eval lazy in fullquote (2 ^ 18) Σ [] O_type indt constt cot.
Definition ty_O :=
  Eval lazy in 
  match prety_O with
  | Success t => t
  | Error _ => sRel 0
  end.

(* S *)
Quote Definition S_type := 
  ltac:(let T := type of S in exact T).
Definition prety_S :=
  Eval lazy in fullquote (2 ^ 18) Σ [] S_type indt constt cot.
Definition ty_S :=
  Eval lazy in 
  match prety_S with
  | Success t => t
  | Error _ => sRel 0
  end.

(* vec *)
Quote Definition vec_type := 
  ltac:(let T := type of vec in exact T).
Definition prety_vec :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vec_type indt constt cot.
Definition ty_vec :=
  Eval lazy in 
  match prety_vec with
  | Success t => t
  | Error _ => sRel 0
  end.

(* vnil *)
Quote Definition vnil_type :=
  ltac:(let T := type of @vnil in exact T).
Definition prety_vnil :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vnil_type indt constt cot.
Definition ty_vnil :=
  Eval lazy in
  match prety_vnil with
  | Success t => t
  | Error _ => sRel 0
  end.

(* vcons *)
Quote Definition vcons_type :=
  ltac:(let T := type of @vcons in exact T).
Definition prety_vcons :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vcons_type indt constt cot.
Definition ty_vcons :=
  Eval lazy in
  match prety_vcons with
  | Success t => t
  | Error _ => sRel 0
  end.

(* vec_rect *)
Quote Definition vec_rect_type :=
  ltac:(let T := type of @vec_rect in exact T).
Definition prety_vec_rect :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vec_rect_type indt constt cot.
Definition ty_vec_rect :=
  Eval lazy in
  match prety_vec_rect with
  | Success t => t
  | Error _ => sRel 0
  end.

(* add *)
Quote Definition add_type :=
  ltac:(let T := type of @Nat.add in exact T).
Definition prety_add :=
  Eval lazy in fullquote (2 ^ 18) Σ [] add_type indt constt cot.
Definition ty_add :=
  Eval lazy in
  match prety_add with
  | Success t => t
  | Error _ => sRel 0
  end.


(* The global context *)

Definition Σi : sglobal_context := [
  (* decl "vrev_obligation4" ty_obligation4 ; *)
  (* decl "vrev_obligation3" ty_obligation3 ; *)
  (* decl "vrev_obligation2" ty_obligation2 ; *)
  (* decl "vrev_obligation1" ty_obligation1 ; *)
  decl "add" ty_add ;
  decl "vec_rect" ty_vec_rect ;
  decl "vcons" ty_vcons ;
  decl "vnil" ty_vnil ;
  decl "vec" ty_vec ;
  decl "S" ty_S ;
  decl "O" ty_O ;
  decl "nat" ty_nat
].

Arguments Σi : simpl never.

Fact hΣi : type_glob Σi.
Proof.
  (* destruct chΣi. assumption. *)
  repeat glob ; lazy.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  (* - ittcheck. *)
  (* - ittcheck. *)
  (* - ittcheck. *)
  (* - ittcheck. *)
  Unshelve. all: exact nAnon.
Defined.

Fact xhΣi : xtype_glob Σi.
Proof.
  (* destruct chΣi. assumption. *)
  repeat xglob ; lazy.
  - ettcheck.
  - ettcheck.
  - ettcheck.
  - ettcheck.
  - ettcheck.
  - ettcheck.
  - ettcheck.
  - ettcheck.
  (* - ettcheck. *)
  (* - ettcheck. *)
  (* - ettcheck. *)
  (* - ettcheck. *)
  Unshelve. all: exact nAnon.
Defined.

Fact istrans_nil :
  ctxtrans Σi nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition type_translation {Γ t A} h {Γ'} hΓ :=
  pi2_ (pi1_ (@complete_translation _ Σi hΣi)) Γ t A h Γ' hΓ.