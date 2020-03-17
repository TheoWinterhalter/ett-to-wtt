From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From Equations Require Import Equations.
From Translation Require Import util SAst SLiftSubst.
From Translation Require Sorts.
Import ListNotations.

Section Common.

Context `{Sort_notion : Sorts.notion}.

Definition scontext := list sterm.

Definition ssnoc (Γ : scontext) (d : sterm) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Delimit Scope s_scope with s.

Record squash (A : Set) : Prop := { _ : A }.

(* Common lemmata *)

(* Lemma max_id : *)
(*   forall s, @Sorts.max Sorts.nat_sorts s s = s. *)
(* Proof. *)
(*   intro s. cbn. auto with arith. *)
(* Defined. *)

(* Lemma max_id : *)
(*   forall s, @Sorts.max Sorts.type_in_type s s = s. *)
(* Proof. *)
(*   intro s. cbn. auto with arith. *)
(* Defined. *)

(* Lemma max_succ_id : *)
(*   forall s, max_sort (succ_sort s) s = succ_sort s. *)
(* Proof. *)
(*   intro s. unfold max_sort, succ_sort. *)
(*   auto with arith. *)
(* Defined. *)

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (sapp_context Γ Γ') (at level 25, Γ' at next level, left associativity) : s_scope.

Fact cat_nil :
  forall {Γ}, Γ ,,, [] = Γ.
Proof.
  reflexivity.
Defined.

Fact nil_cat :
  forall {Γ}, [] ,,, Γ = Γ.
Proof.
  induction Γ.
  - reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact length_cat :
  forall {A} {Γ Δ : list A}, #|Γ ++ Δ| = (#|Γ| + #|Δ|)%nat.
Proof.
  intros A Γ. induction Γ ; intro Δ.
  - cbn. reflexivity.
  - cbn. f_equal. apply IHΓ.
Defined.

(** Global contexts of axioms
    Basically a list of ITT types.
 *)
Record glob_decl := { dname : ident ; dtype : sterm }.

Definition sglobal_context : Type := list glob_decl.

Fixpoint lookup_glob (Σ : sglobal_context) (id : ident) : option sterm :=
  match Σ with
  | nil => None
  | d :: Σ =>
    if ident_eq id (dname d) then Some (dtype d)
    else lookup_glob Σ id
  end.

(* Lifting of context *)

Fixpoint lift_context n Γ : scontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift n #|Γ| A) :: (lift_context n Γ)
  end.

Fact lift_context0 :
  forall {Γ}, lift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite lift00. rewrite IHΓ. reflexivity.
Defined.

Fact lift_context_length :
  forall {k Ξ}, #|lift_context k Ξ| = #|Ξ|.
Proof.
  intros k Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

(* Substitution in context *)

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (A{ #|Δ| := u }) :: (subst_context u Δ)
  end.

Fact subst_context_length :
  forall {u Ξ}, #|subst_context u Ξ| = #|Ξ|.
Proof.
  intros u Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

End Common.

Delimit Scope s_scope with s.
Notation " Γ ,, d " :=
  (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Notation " Γ  ,,, Γ' " :=
  (sapp_context Γ Γ')
    (at level 25, Γ' at next level, left associativity) : s_scope.