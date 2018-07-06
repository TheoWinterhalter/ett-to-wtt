Require Import TypingFlags.Loader.
Set Type In Type.

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker.
From Translation Require Import util Sorts SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Quotes Translation FinalTranslation
                                FullQuote ExamplesUtil ExampleQuotes XChecking.

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

(* TODO Move in ExamplesUtil *)
Fixpoint Prods (Γ : scontext) (T : sterm) :=
  match Γ with
  | A :: Γ => Prods Γ (sProd nAnon A T)
  | [] => T
  end.

(* Lemma close_goal_ex : *)
(*   forall {Σ Γ Δ t T}, *)
(*     Σ ;;; Δ |-x t : Prods Γ T -> *)
(*     Σ ;;; Δ ,,, Γ |-x T : Ty -> *)
(*     ∑ t', Σ ;;; Δ ,,, Γ |-x t' : T. *)
(* Proof. *)
(*   intros Σ Γ Δ t T h hT. *)
(*   revert Δ t T h hT. induction Γ as [| A Γ]. *)
(*   - intros Δ t T h hT. *)
(*     rewrite cat_nil. eexists. eassumption. *)
(*   - intros Δ t T h hT. cbn in h. *)
(*     destruct (IHΓ _ _ _ h) as [t' ht']. *)
(*     + admit. *)
(*     +  *)



Lemma close_goal_ex :
  forall {Σ Γ t T},
    Σ ;;; [] |-x t : Prods Γ T ->
    Σ ;;; Γ |-x T : Ty ->
    ∑ t', Σ ;;; Γ |-x t' : T.
Proof.
  intros Σ Γ t T h hT.
  revert t T h hT. induction Γ as [| A Γ].
  - intros t T h hT. eexists. eassumption.
  - intros t T h hT. cbn in h.
    destruct (IHΓ _ _ h) as [t' ht'].
    + pose proof (typing_wf hT) as hw.
      inversion hw. subst. destruct s.
      eapply xtype_Prod'.
      * eassumption.
      * intros _. eassumption.
    + eexists. eapply xmeta_conv.
      * eapply xtype_App'.
        -- (* Need type_lift *)
Admitted.

Definition closet {Σ Γ t T} h hT :=
  let '(t' ; _) := @close_goal_ex Σ Γ t T h hT in t'.

Definition close_goal :
  forall {Σ Γ t T}
    (h : Σ ;;; [] |-x t : Prods Γ T)
    (hT : Σ ;;; Γ |-x T : Ty),
    Σ ;;; Γ |-x closet h hT : T.
Proof.
  intros Σ Γ t T h hT.
  eapply close_goal_ex.
Defined.





(* Lemma type_vrev : Σi ;;; [] |-x tm_vrev : ty_vrev. *)
(* Proof. *)
(*   unfold tm_vrev, ty_vrev. *)
(*   ettcheck. *)
(*   - eapply close_goal. *)
(*     eapply reflection with (e := sAx "vrev_obligation1"). *)
(*     (* It would need the exact same type to work, *)
(*        names are going to be a problem otherwise. *)
(*      *) *)
(*     ettcheck. *)

(*   - instantiate (1 := nNamed "m"). *)
(*     eapply reflection. *)
(*     instantiate (1 := sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation1") _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)). *)
(*     ettcheck. *)
(*     Opaque Σi. *)
(*     all: lazy. *)
(*     all: try eapply eq_reflexivity. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + lazy. ettcheck. *)
(*     + ettcheck. *)
(*     + lazy. ettcheck. *)
(*     + ettcheck. *)
(*     + lazy. ettcheck. *)
(*     + ettcheck. *)
(*     + lazy. ettcheck. *)
(*     + ettcheck. *)
(*     + lazy. ettcheck. *)
(*     + ettcheck. *)
(*     + lazy. ettcheck. *)
(*     + ettcheck. *)
(*   - Opaque Σi. lazy. eapply reflection. *)
(*     instantiate (2 := sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation2") _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)). *)
(*     ettcheck. *)
(*     all: lazy. *)
(*     all: try eapply eq_reflexivity. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*   - Opaque Σi. lazy. eapply reflection. *)
(*     instantiate (1 := sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation3") _ _ (sRel 10)) _ _ (sRel 9)) _ _ (sRel 8)) _ _ (sRel 7)) _ _ (sRel 6)) _ _ (sRel 5)) _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)). *)
(*     ettcheck. *)
(*     all: lazy. *)
(*     all: try eapply eq_reflexivity. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*   - Opaque Σi. lazy. eapply reflection. *)
(*     instantiate (2 := sApp (sApp (sApp (sApp (sApp (sAx "vrev_obligation2") _ _ (sRel 4)) _ _ (sRel 3)) _ _ (sRel 2)) _ _ (sRel 1)) _ _ (sRel 0)). *)
(*     ettcheck. *)
(*     all: lazy. *)
(*     all: try eapply eq_reflexivity. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. *)
(*     + ettcheck. lazy. ettcheck. *)
(* Defined. *)

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