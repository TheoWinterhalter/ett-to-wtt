(*! Notion of sort *)

From Template Require Import Ast.
From Translation Require Import util.

Class notion := {
  sort : Type ;
  succ : sort -> sort ;
  max : sort -> sort -> sort
}.

Local Instance nat_sorts : notion := {|
  sort := nat ;
  succ := S ;
  max := Nat.max
|}.

Local Instance type_in_type : notion := {|
  sort := unit ;
  succ u := u ;
  max u v := tt
|}.