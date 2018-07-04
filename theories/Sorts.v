(*! Notion of sort *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template Require Import Ast.
From Translation Require Import util.

Class notion := {
  sort : Type ;
  succ : sort -> sort ;
  max : sort -> sort -> sort ;
  eq_dec : forall s z : sort, {s = z} + {s <> z} ;
  succ_inj : forall s z, succ s = succ z -> s = z
}.

Local Instance nat_sorts : notion := {|
  sort := nat ;
  succ := S ;
  max := Nat.max ;
  eq_dec := Nat.eq_dec
|}.
Proof.
  intros s z e. auto with arith.
Defined.

Local Instance type_in_type : notion := {|
  sort := unit ;
  succ u := u ;
  max u v := tt
|}.
Proof.
  - intros [] []. left. reflexivity.
  - intros [] [] _. reflexivity.
Defined.
