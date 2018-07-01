(*! General utilities to build ETT derivations and terms *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import utils Ast LiftSubst Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible XTyping
     FundamentalLemma Translation FinalTranslation FullQuote.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

(* The context for Template Coq *)

Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

Definition axiom_nat_ty := ltac:(let t := type of axiom_nat in exact t).
Definition axiom_zero_ty := ltac:(let t := type of axiom_zero in exact t).
Definition axiom_succ_ty := ltac:(let t := type of axiom_succ in exact t).
Definition axiom_nat_rect_ty :=
  ltac:(let t := type of axiom_nat_rect in exact t).
Definition axiom_nat_rect_zero_ty :=
  ltac:(let t := type of axiom_nat_rect_zero in exact t).
Definition axiom_nat_rect_succ_ty :=
  ltac:(let t := type of axiom_nat_rect_succ in exact t).

Definition axiom_vec_ty := ltac:(let t := type of axiom_vec in exact t).
Definition axiom_vnil_ty := ltac:(let t := type of axiom_vnil in exact t).
Definition axiom_vcons_ty := ltac:(let t := type of axiom_vcons in exact t).
Definition axiom_vec_rect_ty :=
  ltac:(let t := type of axiom_vec_rect in exact t).
Definition axiom_vec_rect_vnil_ty :=
  ltac:(let t := type of axiom_vec_rect_vnil in exact t).
Definition axiom_vec_rect_vcons_ty :=
  ltac:(let t := type of axiom_vec_rect_vcons in exact t).

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
  (* Axiomatising nat *)
  let _ := @axiom_nat in
  let _ := @axiom_nat_ty in
  let _ := @axiom_zero in
  let _ := @axiom_zero_ty in
  let _ := @axiom_succ in
  let _ := @axiom_succ_ty in
  let _ := @axiom_nat_rect in
  let _ := @axiom_nat_rect_ty in
  let _ := @axiom_nat_rect_zero in
  let _ := @axiom_nat_rect_zero_ty in
  let _ := @axiom_nat_rect_succ in
  let _ := @axiom_nat_rect_succ_ty in
  (* Vec *)
  let _ := @axiom_vec in
  let _ := @axiom_vnil in
  let _ := @axiom_vcons in
  let _ := @axiom_vec_rect in
  let _ := @axiom_vec_rect_vnil in
  let _ := @axiom_vec_rect_vcons in
  let _ := @axiom_vec_ty in
  let _ := @axiom_vnil_ty in
  let _ := @axiom_vcons_ty in
  let _ := @axiom_vec_rect_ty in
  let _ := @axiom_vec_rect_vnil_ty in
  let _ := @axiom_vec_rect_vcons_ty in
  (* Candidate *)
  let _ := @candidate in
  Type.

Quote Recursively Definition glob_prog := @glob_term.
Definition Σ : global_context :=
  (* reconstruct_global_context (Datatypes.fst glob_prog). *)
  pair (Datatypes.fst glob_prog) init_graph.

(* Definition Σ := ltac:(let t := eval lazy in Σ' in exact t). *)

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

(* Getting axiom_nat as an axiom for ITT/ETT *)
Quote Recursively Definition taxiom_nat_ty := axiom_nat_ty.
Definition ttaxiom_nat_ty :=
  let t := Datatypes.snd taxiom_nat_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_nat_ty :=
  ltac:(let u := eval lazy in ttaxiom_nat_ty in exact u).

Definition fq_ax_nat_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_nat_ty.
Definition rfq_ax_nat_ty :=
  ltac:(let u := eval lazy in fq_ax_nat_ty in exact u).
Definition ax_nat_ty :=
  match rfq_ax_nat_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_nat_ty :=
  ltac:(let u := eval lazy in ax_nat_ty in exact u).

(* Getting axiom_nat_rect as an axiom for ITT/ETT *)
Quote Recursively Definition taxiom_nat_rect_ty := axiom_nat_rect_ty.
Definition ttaxiom_nat_rect_ty :=
  let t := Datatypes.snd taxiom_nat_rect_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_nat_rect_ty :=
  ltac:(let u := eval lazy in ttaxiom_nat_rect_ty in exact u).

(* Variable axf' : nat -> sort. *)

(* Maybe we shouldn't use 0 for all sorts. *)
(* Definition axf (i : nat) := *)
(*   match i with *)
(*   | i => 0 *)
(*   end. *)

Definition fq_ax_nat_rect_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_nat_rect_ty.
Definition rfq_ax_nat_rect_ty :=
  ltac:(let u := eval lazy in fq_ax_nat_rect_ty in exact u).
Definition ax_nat_rect_ty :=
  match rfq_ax_nat_rect_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_nat_rect_ty :=
  ltac:(let u := eval lazy in ax_nat_rect_ty in exact u).



(* axiom_nat_rect_zero *)
Quote Recursively Definition taxiom_nat_rect_zero_ty := axiom_nat_rect_zero_ty.
Definition ttaxiom_nat_rect_zero_ty :=
  let t := Datatypes.snd taxiom_nat_rect_zero_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_nat_rect_zero_ty :=
  ltac:(let u := eval lazy in ttaxiom_nat_rect_zero_ty in exact u).
Definition fq_ax_nat_rect_zero_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_nat_rect_zero_ty.
Definition rfq_ax_nat_rect_zero_ty :=
  ltac:(let u := eval lazy in fq_ax_nat_rect_zero_ty in exact u).
Definition ax_nat_rect_zero_ty :=
  match rfq_ax_nat_rect_zero_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_nat_rect_zero_ty :=
  ltac:(let u := eval lazy in ax_nat_rect_zero_ty in exact u).



(* axiom_nat_rect_succ *)
Quote Recursively Definition taxiom_nat_rect_succ_ty := axiom_nat_rect_succ_ty.
Definition ttaxiom_nat_rect_succ_ty :=
  let t := Datatypes.snd taxiom_nat_rect_succ_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_nat_rect_succ_ty :=
  ltac:(let u := eval lazy in ttaxiom_nat_rect_succ_ty in exact u).
Definition fq_ax_nat_rect_succ_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_nat_rect_succ_ty.
Definition rfq_ax_nat_rect_succ_ty :=
  ltac:(let u := eval lazy in fq_ax_nat_rect_succ_ty in exact u).
Definition ax_nat_rect_succ_ty :=
  match rfq_ax_nat_rect_succ_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_nat_rect_succ_ty :=
  ltac:(let u := eval lazy in ax_nat_rect_succ_ty in exact u).



(* axiom_vec *)
Quote Recursively Definition taxiom_vec_ty := axiom_vec_ty.
Definition ttaxiom_vec_ty :=
  let t := Datatypes.snd taxiom_vec_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_vec_ty :=
  ltac:(let u := eval lazy in ttaxiom_vec_ty in exact u).
Definition fq_ax_vec_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_vec_ty.
Definition rfq_ax_vec_ty :=
  ltac:(let u := eval lazy in fq_ax_vec_ty in exact u).
Definition ax_vec_ty :=
  match rfq_ax_vec_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_vec_ty :=
  ltac:(let u := eval lazy in ax_vec_ty in exact u).



(* axiom_vnil *)
Quote Recursively Definition taxiom_vnil_ty := axiom_vnil_ty.
Definition ttaxiom_vnil_ty :=
  let t := Datatypes.snd taxiom_vnil_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_vnil_ty :=
  ltac:(let u := eval lazy in ttaxiom_vnil_ty in exact u).
Definition fq_ax_vnil_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_vnil_ty.
Definition rfq_ax_vnil_ty :=
  ltac:(let u := eval lazy in fq_ax_vnil_ty in exact u).
Definition ax_vnil_ty :=
  match rfq_ax_vnil_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_vnil_ty :=
  ltac:(let u := eval lazy in ax_vnil_ty in exact u).



(* axiom_vcons *)
Quote Recursively Definition taxiom_vcons_ty := axiom_vcons_ty.
Definition ttaxiom_vcons_ty :=
  let t := Datatypes.snd taxiom_vcons_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_vcons_ty :=
  ltac:(let u := eval lazy in ttaxiom_vcons_ty in exact u).
Definition fq_ax_vcons_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_vcons_ty.
Definition rfq_ax_vcons_ty :=
  ltac:(let u := eval lazy in fq_ax_vcons_ty in exact u).
Definition ax_vcons_ty :=
  match rfq_ax_vcons_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_vcons_ty :=
  ltac:(let u := eval lazy in ax_vcons_ty in exact u).



(* axiom_vec_rect *)
Quote Recursively Definition taxiom_vec_rect_ty := axiom_vec_rect_ty.
Definition ttaxiom_vec_rect_ty :=
  let t := Datatypes.snd taxiom_vec_rect_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_vec_rect_ty :=
  ltac:(let u := eval lazy in ttaxiom_vec_rect_ty in exact u).
Definition fq_ax_vec_rect_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_vec_rect_ty.
Definition rfq_ax_vec_rect_ty :=
  ltac:(let u := eval lazy in fq_ax_vec_rect_ty in exact u).
Definition ax_vec_rect_ty :=
  match rfq_ax_vec_rect_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_vec_rect_ty :=
  ltac:(let u := eval lazy in ax_vec_rect_ty in exact u).



(* axiom_vec_rect_vnil *)
Quote Recursively Definition taxiom_vec_rect_vnil_ty := axiom_vec_rect_vnil_ty.
Definition ttaxiom_vec_rect_vnil_ty :=
  let t := Datatypes.snd taxiom_vec_rect_vnil_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_vec_rect_vnil_ty :=
  ltac:(let u := eval lazy in ttaxiom_vec_rect_vnil_ty in exact u).
Definition fq_ax_vec_rect_vnil_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_vec_rect_vnil_ty.
Definition rfq_ax_vec_rect_vnil_ty :=
  ltac:(let u := eval lazy in fq_ax_vec_rect_vnil_ty in exact u).
Definition ax_vec_rect_vnil_ty :=
  match rfq_ax_vec_rect_vnil_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_vec_rect_vnil_ty :=
  ltac:(let u := eval lazy in ax_vec_rect_vnil_ty in exact u).



(* axiom_vec_rect_vcons *)
Quote Recursively Definition taxiom_vec_rect_vcons_ty := axiom_vec_rect_vcons_ty.
Definition ttaxiom_vec_rect_vcons_ty :=
  let t := Datatypes.snd taxiom_vec_rect_vcons_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_vec_rect_vcons_ty :=
  ltac:(let u := eval lazy in ttaxiom_vec_rect_vcons_ty in exact u).
Definition fq_ax_vec_rect_vcons_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_vec_rect_vcons_ty.
Definition rfq_ax_vec_rect_vcons_ty :=
  ltac:(let u := eval lazy in fq_ax_vec_rect_vcons_ty in exact u).
Definition ax_vec_rect_vcons_ty :=
  match rfq_ax_vec_rect_vcons_ty with
  | Success t => t
  | _ => sRel 0
  end.
Definition rtax_vec_rect_vcons_ty :=
  ltac:(let u := eval lazy in ax_vec_rect_vcons_ty in exact u).




(* The global context *)

Definition Σi : sglobal_context := [
  decl "vec_rect_vcons" rtax_vec_rect_vcons_ty ;
  decl "vec_rect_vnil" rtax_vec_rect_vnil_ty ;
  decl "vec_rect" rtax_vec_rect_ty ;
  decl "vcons" rtax_vcons_ty ;
  decl "vnil" rtax_vnil_ty ;
  decl "vec" rtax_vec_ty ;
  decl "nat_rect_succ" rtax_nat_rect_succ_ty ;
  decl "nat_rect_zero" rtax_nat_rect_zero_ty ;
  decl "nat_rect" rtax_nat_rect_ty ;
  decl "succ" (sAx "nat" ==> sAx "nat") ;
  decl "zero" (sAx "nat") ;
  decl "nat" rtax_nat_ty
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

Definition pn := nNamed "pppp".

Fixpoint multiProd (bl : list sterm) :=
  match bl with
  | [] => sSort (succ tt)
  | [ A ] => A
  | A :: bl => sProd pn A (multiProd bl)
  end.

Fixpoint multiLam (bl : list sterm) (t : sterm) :=
  match bl with
  | [] => sSort tt
  | [ A ] => t
  | A :: bl => sLambda pn A (multiProd bl) (multiLam bl t)
  end.

Inductive wfb : scontext -> list sterm -> Type :=
| wfb_nil Γ : wfb Γ []
| wfb_cons Γ A s bl :
    Σi ;;; Γ |-x A : sSort s ->
    wfb (A :: Γ) bl ->
    wfb Γ (A :: bl).

Derive Signature for wfb.

Lemma type_multiProd :
  forall {bl Γ},
    wf Σi Γ ->
    wfb Γ bl ->
    ∑ s,
      Σi ;;; Γ |-x multiProd bl : sSort s.
Proof.
  intro bl. induction bl ; intros Γ hwf h.
  - cbn. exists (@succ Sorts.type_in_type tt). apply type_Sort. assumption.
  - destruct bl.
    + cbn. dependent destruction h.
      eexists. eassumption.
    + change (multiProd (a :: s :: bl))
        with (sProd pn a (multiProd (s :: bl))).
      dependent destruction h.
      dependent destruction h.
      destruct (IHbl (ssnoc Γ0 A)) as [z hz].
      * econstructor.
        -- assumption.
        -- eassumption.
      * econstructor.
        -- eassumption.
        -- assumption.
      * eexists. eapply type_Prod.
        -- eassumption.
        -- exact hz.
Defined.

Inductive wbtm : scontext -> list sterm -> sterm -> Type :=
| wbtm_nil Γ t : wbtm Γ [] t
| wbtm_one Γ A s t :
    Σi ;;; Γ |-x A : sSort s ->
    Σi ;;; Γ |-x t : A ->
    wbtm Γ [ A ] t
| wbtm_cons Γ A B s bl t :
    Σi ;;; Γ |-x A : sSort s ->
    wbtm (A :: Γ) (B :: bl) t ->
    wbtm Γ (A :: B :: bl) t.

Derive Signature for wbtm.

Lemma wbtm_wfb :
  forall {bl Γ t},
    wbtm Γ bl t ->
    wfb Γ bl.
Proof.
  intro bl. induction bl ; intros Γ t h.
  - constructor.
  - destruct bl.
    + dependent destruction h.
      econstructor.
      * eassumption.
      * constructor.
    + dependent destruction h.
      econstructor.
      * eassumption.
      * eapply IHbl. eassumption.
Defined.

Lemma type_multiLam :
  forall {bl Γ t},
    wf Σi Γ ->
    wbtm Γ bl t ->
    Σi ;;; Γ |-x multiLam bl t : multiProd bl.
Proof.
  intro bl. induction bl ; intros Γ t hwf hwb.
  - cbn. refine (type_Sort _ _ _ _). assumption.
  - destruct bl.
    + cbn. dependent destruction hwb. assumption.
    + change (multiProd (a :: s :: bl))
        with (sProd pn a (multiProd (s :: bl))).
      change (multiLam (a :: s :: bl) t)
        with (sLambda pn a (multiProd (s :: bl)) (multiLam (s :: bl) t)).
      dependent destruction hwb.
      destruct (@type_multiProd (B :: bl0) (ssnoc Γ0 A)) as [z hz].
      * econstructor.
        -- assumption.
        -- eassumption.
      * eapply wbtm_wfb. eassumption.
      * eapply type_Lambda.
        -- eassumption.
        -- eassumption.
        -- eapply IHbl.
           ++ econstructor.
              ** assumption.
              ** eassumption.
           ++ assumption.
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