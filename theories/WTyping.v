(*! WTT Typing *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util Sorts WAst WLiftSubst.

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
Record glob_decl := { dname : ident ; dtype : wterm }.

Definition wglobal_context : Type := list glob_decl.

Fixpoint lookup_glob (Σ : wglobal_context) (id : ident) : option wterm :=
  match Σ with
  | nil => None
  | d :: Σ =>
    if ident_eq id (dname d) then Some (dtype d)
    else lookup_glob Σ id
  end.

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

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-w t : wSort s1 ->
    Σ ;;; Γ ,, t |-w b : wSort s2 ->
    Σ ;;; Γ |-w wProd n t b : wSort (Sorts.prod_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-w t : wSort s1 ->
    Σ ;;; Γ ,, t |-w bty : wSort s2 ->
    Σ ;;; Γ ,, t |-w b : bty ->
    Σ ;;; Γ |-w wLambda n t b : wProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-w A : wSort s1 ->
    Σ ;;; Γ ,, A |-w B : wSort s2 ->
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

| type_Beta Γ A B t u n :
    Σ ;;; Γ ,, A |-w t : B ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w wBeta t u : wEq (B{ 0 := u })
                               (wApp (wLambda n A t) u)
                               (t{ 0 := u })

| type_Heq Γ A a B b s :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ |-w a : A ->
    Σ ;;; Γ |-w b : B ->
    Σ ;;; Γ |-w wHeq A a B b : wSort s

| type_HeqPair Γ A a B b s p q :
    Σ ;;; Γ |-w a : A ->
    Σ ;;; Γ |-w b : B ->
    Σ ;;; Γ |-w p : wEq (wSort s) A B ->
    Σ ;;; Γ |-w q : wEq B (wTransport A B p a) b ->
    Σ ;;; Γ |-w wHeq A a B b : wSort s

| type_HeqTy Γ A a B b p s :
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ |-w p : wHeq A a B b ->
    Σ ;;; Γ |-w wHeqTy p : wEq (wSort s) A B

| type_HeqTm Γ A a B b p :
    Σ ;;; Γ |-w p : wHeq A a B b ->
    Σ ;;; Γ |-w wHeqTm p : wEq B (wTransport A B (wHeqTy p) a) b

| type_Pack Γ A1 A2 s :
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w wPack A1 A2 : wSort s

| type_ProjT1 Γ A1 A2 p s :
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w p : wPack A1 A2 ->
    Σ ;;; Γ |-w wProjT1 p : A1

| type_ProjT2 Γ A1 A2 p s :
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w p : wPack A1 A2 ->
    Σ ;;; Γ |-w wProjT2 p : A2

| type_ProjTe Γ A1 A2 p s :
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w p : wPack A1 A2 ->
    Σ ;;; Γ |-w wProjTe p : wHeq A1 (wProjT1 p) A2 (wProjT2 p)

| type_Ax Γ id ty :
    wf Σ Γ ->
    lookup_glob Σ id = Some ty ->
    Σ ;;; Γ |-w wAx id : ty

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

(* TODO: What should be done abut this in WTT? Only rehabilitate if necessary. *)
(* Section Global. *)

(* Context `{Sort_notion : Sorts.notion}. *)

(* Definition isType (Σ : wglobal_context) (Γ : wcontext) (t : wterm) := *)
(*   exists s, Σ ;;; Γ |-w t : wSort s. *)

(* Inductive fresh_glob (id : ident) : wglobal_context -> Prop := *)
(* | fresh_glob_nil : fresh_glob id [] *)
(* | fresh_glob_cons Σ d : *)
(*     fresh_glob id Σ -> *)
(*     (dname d) <> id -> *)
(*     fresh_glob id (d :: Σ). *)

(* Inductive type_glob : wglobal_context -> Type := *)
(* | type_glob_nil : type_glob [] *)
(* | type_glob_cons Σ d : *)
(*     type_glob Σ -> *)
(*     fresh_glob (dname d) Σ -> *)
(*     isType Σ [] (dtype d) -> *)
(*     Xcomp (dtype d) -> *)
(*     type_glob (d :: Σ). *)

(* End Global. *)

(* Derive Signature for fresh_glob. *)
(* Derive Signature for type_glob. *)
