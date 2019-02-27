(*! WTT Typing *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util Sorts WAst WLiftSubst WEquality.

Open Scope w_scope.

(* Preliminaries *)
Section Prelim.

Context `{Sort_notion : Sorts.notion}.

Definition wcontext := list wterm.

Definition wsnoc (Γ : wcontext) (d : wterm) := d :: Γ.

Notation " Γ ,, d " := (wsnoc Γ d) (at level 20, d at next level) : w_scope.

(** Global contexts of axioms
    Basically a list of ITT types.
 *)
Record glob_decl := { dname : ident ; dtype : wterm ; dbody : wterm }.

Definition wglobal_context : Type := list glob_decl.

Definition lookup_glob (Σ : wglobal_context) (id : ident) :=
  List.find (fun d => ident_eq id (dname d)) Σ.

End Prelim.

(*! Typing *)

Section WTyping.

Context `{Sort_notion : Sorts.notion}.

Reserved Notation " Σ ;;; Γ '|-w' t : T " (at level 50, Γ, t, T at next level).

Inductive typing (Σ : wglobal_context) : wcontext -> wterm -> wterm -> Prop :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-w (wRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl))

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-w (wSort s) : wSort (Sorts.succ s)

| type_Prod Γ n A B s1 s2 :
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ ,, A |-w B : wSort s2 ->
    Σ ;;; Γ |-w wProd n A B : wSort (Sorts.prod_sort s1 s2)

| type_Lambda Γ n n' t s A B :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ ,, A |-w t : B ->
    Σ ;;; Γ |-w wLambda n A t : wProd n' A B

| type_App Γ n t A B u :
    Σ ;;; Γ |-w t : wProd n A B ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wApp t u : B{ 0 := u }

| type_Sum Γ n t b s1 s2 :
    Σ ;;; Γ |-w t : wSort s1 ->
    Σ ;;; Γ ,, t |-w b : wSort s2 ->
    Σ ;;; Γ |-w (wSum n t b) : wSort (Sorts.sum_sort s1 s2)

| type_Pair Γ n A B u v s1 s2 :
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ ,, A |-w B : wSort s2 ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w v : B{ 0 := u } ->
    Σ ;;; Γ |-w wPair A B u v : wSum n A B

| type_Pi1 Γ n A B s1 s2 p :
    Σ ;;; Γ |-w p : wSum n A B ->
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ ,, A |-w B : wSort s2 ->
    Σ ;;; Γ |-w wPi1 A B p : A

| type_Pi2 Γ n A B s1 s2 p :
    Σ ;;; Γ |-w p : wSum n A B ->
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ ,, A |-w B : wSort s2 ->
    Σ ;;; Γ |-w wPi2 A B p : B{ 0 := wPi1 A B p }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w v : A ->
    Σ ;;; Γ |-w wEq A u v : wSort (Sorts.eq_sort s)

| type_Refl Γ s A u :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wRefl A u : wEq A u u

| type_J Γ s1 s2 A u v P p w :
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w v : A ->
    Σ ;;; Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0)) |-w P : wSort s2 ->
    Σ ;;; Γ |-w p : wEq A u v ->
    Σ ;;; Γ |-w w : P{ 1 := u }{ 0 := wRefl A u } ->
    Σ ;;; Γ |-w wJ A u P w v p : P{ 1 := v }{ 0 := p }

| type_Transport Γ s T1 T2 p t :
    Σ ;;; Γ |-w T1 : wSort s ->
    Σ ;;; Γ |-w T2 : wSort s ->
    Σ ;;; Γ |-w p : wEq (wSort s) T1 T2 ->
    Σ ;;; Γ |-w t : T1 ->
    Σ ;;; Γ |-w wTransport T1 T2 p t : T2

| type_Beta Γ s A B t u n :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ ,, A |-w t : B ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wBeta t u : wEq (B{ 0 := u })
                               (wApp (wLambda n A t) u)
                               (t{ 0 := u })

| type_K Γ A u p s :
    Σ ;;; Γ |-w p : wEq A u u ->
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wK A u p : wEq (wEq A u u) p (wRefl A u)

| type_Funext Γ A B f g p n nx n1 n2 :
    Σ ;;; Γ |-w p : wProd nx A
                     (wEq B (wApp (lift0 1 f) (wRel 0))
                            (wApp (lift0 1 g) (wRel 0))) ->
    Σ ;;; Γ |-w f : wProd n1 A B ->
    Σ ;;; Γ |-w g : wProd n2 A B ->
    Σ ;;; Γ |-w wFunext f g p : wEq (wProd n A B) f g

| type_JBeta Γ A u P w s1 s2 :
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0)) |-w P : wSort s2 ->
    Σ ;;; Γ |-w w : P{ 1 := u }{ 0 := wRefl A u } ->
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ |-w wJBeta u P w : wEq (P{ 1 := u }{ 0 := wRefl A u })
                                (wJ A u P w u (wRefl A u))
                                w

| type_TransportBeta Γ s A t :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w wTransportBeta A t
             : wEq A (wTransport A A (wRefl (wSort s) A) t) t

| type_PairEta Γ A B p n n' :
    Σ ;;; Γ |-w p : wSum n A B ->
    Σ ;;; Γ |-w wPairEta p
             : wEq (wSum n' A B) (wPair A B (wPi1 A B p) (wPi2 A B p)) p

| type_Ax Γ id d :
    wf Σ Γ ->
    lookup_glob Σ id = Some d ->
    Σ ;;; Γ |-w wAx id : dtype d

| type_Delta Γ id d :
    wf Σ Γ ->
    lookup_glob Σ id = Some d ->
    Σ ;;; Γ |-w wDelta id : wEq (dtype d) (wAx id) (dbody d)

| type_rename Γ t A B :
    Σ ;;; Γ |-w t : A ->
    nl A = nl B ->
    Σ ;;; Γ |-w t : B

where " Σ ;;; Γ '|-w' t : T " := (@typing Σ Γ t T) : w_scope

with wf (Σ : wglobal_context) : wcontext -> Prop :=
| wf_nil :
    wf Σ nil

| wf_snoc s Γ A :
    wf Σ Γ ->
    Σ ;;; Γ |-w A : wSort s ->
    wf Σ (Γ ,, A)
.

End WTyping.

Notation " Σ ;;; Γ '|-w' t : T " :=
  (@typing _ Σ Γ t T) (at level 50, Γ, t, T at next level) : w_scope.

Derive Signature for typing.
Derive Signature for wf.

Delimit Scope w_scope with w.

Section Global.

Context `{Sort_notion : Sorts.notion}.

Definition isType (Σ : wglobal_context) (Γ : wcontext) (t : wterm) :=
  exists s, Σ ;;; Γ |-w t : wSort s.

Inductive fresh_glob (id : ident) : wglobal_context -> Prop :=
| fresh_glob_nil : fresh_glob id []
| fresh_glob_cons Σ d :
    fresh_glob id Σ ->
    (dname d) <> id ->
    fresh_glob id (d :: Σ).

Inductive type_glob : wglobal_context -> Type :=
| type_glob_nil : type_glob []
| type_glob_cons Σ d :
    type_glob Σ ->
    fresh_glob (dname d) Σ ->
    isType Σ [] (dtype d) ->
    Σ ;;; [] |-w dbody d : dtype d ->
    type_glob (d :: Σ).

End Global.

Derive Signature for fresh_glob.
Derive Signature for type_glob.
