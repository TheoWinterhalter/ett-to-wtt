(*! General utilities to build ETT derivations and terms *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import utils Ast LiftSubst Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible XTyping
     FundamentalLemma Translation FinalTranslation FullQuote ExampleQuotes.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

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
  let _ := vrev_eq0 in
  let _ := vrev_eq1 in
  Type.

Quote Recursively Definition glob_prog := @glob_term.
Definition Σ : global_context :=
  (* Eval lazy in *)
  (* reconstruct_global_context (Datatypes.fst glob_prog). *)
  pair (Datatypes.fst glob_prog) init_graph.

Arguments Σ : simpl never.

Open Scope string_scope.
Open Scope s_scope.

Module IT := ITyping.
Module IL := ITypingLemmata.

(* The context for ITT *)

Definition decl := Build_glob_decl.

Definition nctx := list (name * sterm).

Fixpoint Sums (L : nctx) (T : sterm) :=
  match L with
  | (na,A) :: L => sSum na A (Sums L T)
  | [] => T
  end.

Fixpoint Prods (L : nctx) (T : sterm) :=
  match L with
  | (na,A) :: L => sProd na A (Prods L T)
  | [] => T
  end.

Definition subst_nctx u (L : nctx) :=
  map_i (fun i '(nx, A) => (nx, A{ i := u })) L.

Definition substn_nctx u n (L : nctx) :=
  map_i_aux (fun i '(nx, A) => (nx, A{ i := u })) n L.

Fixpoint Apps (f : sterm) (L : nctx) (T : sterm) (l : list sterm) : sterm :=
  match L, l with
  | (nx,A) :: L, u :: l =>
    Apps (sApp f A (Prods L T) u) (subst_nctx u L) (T{ #|L| := u }) l
  | _,_ => f
  end.

Definition Arrow A B := sProd nAnon A (lift0 1 B).
Notation "A ==> B" := (Arrow A B) (at level 20, right associativity).

(* Some admissible lemmata to do memoisation in a way. *)
Lemma type_Prod' :
  forall {Σ Γ n A B s1 s2},
    Σ ;;; Γ |-i A : sSort s1 ->
    (IT.wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i B : sSort s2) ->
    Σ ;;; Γ |-i sProd n A B : sSort (Sorts.max s1 s2).
Proof.
  intros Σ' Γ n A B s1 s2 hA hB.
  eapply IT.type_Prod.
  - assumption.
  - apply hB. econstructor ; try eassumption.
    eapply IL.typing_wf. eassumption.
Defined.

Lemma type_Lambda' :
  forall {Σ Γ n n' A B t s},
    type_glob Σ ->
    Σ ;;; Γ |-i A : sSort s ->
    (IT.wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i t : B) ->
    Σ ;;; Γ |-i sLambda n A B t : sProd n' A B.
Proof.
  intros Σ Γ n n' A B t s hg hA ht.
  assert (hw : IT.wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply IL.typing_wf. eassumption.
  }
  specialize (ht hw). destruct (istype_type hg ht).
  eapply IT.type_Lambda ; eassumption.
Defined.

Lemma type_App' :
  forall {Σ Γ n t A B u},
    type_glob Σ ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sApp t A B u : (B{0 := u})%s.
Proof.
  intros Σ Γ n t A B u hg ht hu.
  destruct (istype_type hg ht).
  destruct (istype_type hg hu).
  ttinv H.
  eapply IT.type_App ; eassumption.
Defined.

Lemma type_Sum' :
  forall {Σ Γ n A B s1 s2},
    Σ ;;; Γ |-i A : sSort s1 ->
    (IT.wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i B : sSort s2) ->
    Σ ;;; Γ |-i sSum n A B : sSort (Sorts.max s1 s2).
Proof.
  intros Σ' Γ n A B s1 s2 hA hB.
  eapply IT.type_Sum.
  - assumption.
  - apply hB. econstructor ; try eassumption.
    eapply IL.typing_wf. eassumption.
Defined.

Lemma type_Refl' :
  forall {Σ Γ A u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u hg h.
  destruct (istype_type hg h).
  eapply IT.type_Refl ; eassumption.
Defined.

(* Maybe move somewhere else *)
Ltac ittintro :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-i ?t : ?T =>
    lazymatch t with
    | sRel ?n => refine (IT.type_Rel _ _ n _ _)
    | sSort _ => eapply IT.type_Sort
    | sProd _ _ _ => eapply type_Prod' ; [| intro ]
    | sLambda _ _ _ _ => eapply type_Lambda' ; [ .. | intro ]
    | sApp _ _ _ _ => eapply type_App'
    | sSum _ _ _ => eapply type_Sum' ; [| intro ]
    | sPair _ _ _ _ => eapply type_Pair'
    | sPi1 _ _ _ => eapply type_Pi1'
    | sPi2 _ _ _ => eapply type_Pi2'
    | sEq _ _ _ => eapply IT.type_Eq
    | sRefl _ _ => eapply type_Refl'
    | sAx _ => eapply IT.type_Ax ; [| lazy ; try reflexivity ]
    | _ => fail "No introduction rule for" t
    end
  | _ => fail "Not applicable"
  end.

Lemma type_glob_cons' :
  forall {Σ d},
    type_glob Σ ->
    fresh_glob (dname d) Σ ->
    (type_glob Σ -> isType Σ [] (dtype d)) ->
    Xcomp (dtype d) ->
    type_glob (d :: Σ).
Proof.
  intros Σ d hg hf hd hx.
  specialize (hd hg).
  econstructor ; eassumption.
Defined.

Ltac glob :=
  first [
    eapply type_glob_nil
  | eapply type_glob_cons' ; [
      idtac
    | repeat (lazy ; econstructor) ; lazy ; try discriminate
    | intro ; eexists
    | repeat econstructor
    ]
  ].

Ltac ittcheck1 :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-i ?t : ?T =>
    first [
      eapply meta_conv ; [ ittintro | lazy ; try reflexivity ]
    | eapply meta_ctx_conv ; [
        eapply meta_conv ; [ ittintro | lazy ; try reflexivity ]
      | cbn ; try reflexivity
      ]
    ]
  | |- IT.wf ?Σ ?Γ => first [ assumption | econstructor ]
  | |- sSort _ = sSort _ => first [ lazy ; reflexivity | shelve ]
  | |- type_glob _ => first [ assumption | glob ]
  | _ => fail "Not applicable"
  end.

Ltac ittcheck' := ittcheck1 ; try (lazy ; omega).

Ltac ittcheck := repeat ittcheck'.

(* Preparing the global context (axioms) for examples *)

Notation "s --> t" := (acons s t) (at level 20).
Notation "[< a ; b ; .. ; c >]" :=
  (a (b (.. (c empty) ..))).
Notation "[< a >]" := (a empty).
Notation "[< >]" := (empty).

(* Notation "[< a --> x ; b --> y ; .. ; c --> z >]" := *)
(*   (acons a x (acons b y .. (acons c z empty) ..)). *)

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

(* vrev_eq0 *)
Quote Definition vrev_eq0_type :=
  ltac:(let T := type of @vrev_eq0 in exact T).
Definition prety_vrev_eq0 :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vrev_eq0_type indt constt cot.
Definition ty_vrev_eq0 :=
  Eval lazy in
  match prety_vrev_eq0 with
  | Success t => t
  | Error _ => sRel 0
  end.

(* vrev_eq1 *)
Quote Definition vrev_eq1_type :=
  ltac:(let T := type of @vrev_eq1 in exact T).
Definition prety_vrev_eq1 :=
  Eval lazy in fullquote (2 ^ 18) Σ [] vrev_eq1_type indt constt cot.
Definition ty_vrev_eq1 :=
  Eval lazy in
  match prety_vrev_eq1 with
  | Success t => t
  | Error _ => sRel 0
  end.


(* The global context *)

Definition Σi : sglobal_context := [
  decl "vrev_eq1" ty_vrev_eq1 ;
  decl "vrev_eq0" ty_vrev_eq0 ;
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
  repeat glob ; lazy.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
  - ittcheck.
Defined.

(* Now some useful lemmata *)

Lemma xmeta_conv :
  forall (Σ : sglobal_context) (Γ : scontext) (t A B : sterm),
    Σ;;; Γ |-x t : A ->
    A = B ->
    Σ;;; Γ |-x t : B.
Proof.
  intros Σ Γ t A B h e.
  destruct e. assumption.
Defined.

Lemma xmeta_eq_conv :
  forall {Σ Γ u v A B},
    Σ ;;; Γ |-x u = v : A ->
    A = B ->
    Σ ;;; Γ |-x u = v : B.
Proof.
  intros Σ Γ u v A B h e.
  destruct e. exact h.
Defined.

Lemma type_conv'' :
  forall {Γ t A B s},
    Σi ;;; Γ |-x t : A ->
    Σi ;;; Γ |-x A = B : sSort s ->
    Σi ;;; Γ |-x B : sSort s ->
    Σi ;;; Γ |-x t : B.
Proof.
  intros Γ t A B s H H0 H1.
  eapply type_conv ; eassumption.
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








(* Same for ETT *)
Lemma xtype_Prod' :
  forall {Σ Γ n A B s1 s2},
    Σ ;;; Γ |-x A : sSort s1 ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : sSort s2) ->
    Σ ;;; Γ |-x sProd n A B : sSort (Sorts.max s1 s2).
Proof.
  intros Σ Γ n A B s1 s2 hA hB.
  eapply type_Prod.
  - assumption.
  - apply hB. econstructor ; try eassumption.
    eapply typing_wf. eassumption.
Defined.

Lemma xtype_Lambda' :
  forall {Σ Γ n n' A B t s1 s2},
    Σ ;;; Γ |-x A : sSort s1 ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : sSort s2) ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x t : B) ->
    Σ ;;; Γ |-x sLambda n A B t : sProd n' A B.
Proof.
  intros Σ Γ n n' A B t s1 s2 hA hB ht.
  assert (hw : wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply typing_wf. eassumption.
  }
  specialize (ht hw). specialize (hB hw).
  eapply type_Lambda ; eassumption.
Defined.

Lemma xtype_App' :
  forall {Σ Γ n t A B u s1 s2},
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x A : sSort s1 ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : sSort s2) ->
    Σ ;;; Γ |-x sApp t A B u : (B{0 := u})%s.
Proof.
  intros Σ Γ n t A B u s1 s2 ht hu hA hB.
  assert (hw : wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply typing_wf. eassumption.
  }
  specialize (hB hw).
  eapply type_App ; eassumption.
Defined.

Lemma xtype_Sum' :
  forall {Σ Γ n A B s1 s2},
    Σ ;;; Γ |-x A : sSort s1 ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : sSort s2) ->
    Σ ;;; Γ |-x sSum n A B : sSort (Sorts.max s1 s2).
Proof.
  intros Σ' Γ n A B s1 s2 hA hB.
  eapply type_Sum.
  - assumption.
  - apply hB. econstructor ; try eassumption.
    eapply typing_wf. eassumption.
Defined.

(* Maybe move somewhere else *)
Ltac ettintro :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-x ?t : ?T =>
    lazymatch t with
    | sRel ?n => refine (type_Rel _ _ n _ _)
    | sSort _ => eapply type_Sort
    | sProd _ _ _ => eapply xtype_Prod' ; [| intro ]
    | sLambda _ _ _ _ => eapply xtype_Lambda' ; [ .. | intro | intro ]
    | sApp _ _ _ _ => eapply xtype_App' ; [ .. | intro ]
    | sSum _ _ _ => eapply xtype_Sum' ; [| intro ]
    | sPair _ _ _ _ => eapply type_Pair
    | sPi1 _ _ _ => eapply type_Pi1
    | sPi2 _ _ _ => eapply type_Pi2
    | sEq _ _ _ => eapply type_Eq
    | sRefl _ _ => eapply type_Refl
    | sAx _ => eapply type_Ax ; [| lazy ; try reflexivity ]
    | _ => fail "No introduction rule for" t
    end
  | _ => fail "Not applicable"
  end.

Ltac ettcheck1 :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-x ?t : ?T =>
    first [
      eapply xmeta_conv ; [ ettintro | lazy ; reflexivity ]
    | eapply type_conv ; [ ettintro | .. ]
    (* | eapply meta_ctx_conv ; [ *)
    (*     eapply meta_conv ; [ ettintro | lazy ; try reflexivity ] *)
    (*   | cbn ; try reflexivity *)
    (*   ] *)
    ]
  | |- wf ?Σ ?Γ => first [ assumption | econstructor ]
  | |- sSort _ = sSort _ => first [ lazy ; reflexivity | shelve ]
  | |- type_glob _ => first [ assumption | glob ]
  | _ => fail "Not applicable"
  end.

Ltac ettcheck' := ettcheck1 ; try (lazy ; omega).

Ltac ettcheck := repeat ettcheck'.