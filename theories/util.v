(* Utility *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From Equations Require Import Equations.
Import List.ListNotations.
Set Primitive Projections.
Open Scope type_scope.

Definition compute_eq {n m : nat} : n = m -> n = m :=
  match Nat.eq_dec n m with
  | left p => fun _ => p
  | right nh => fun h => False_rect _ (nh h)
  end.

Definition compute_neq {n m : nat} : n <> m -> n <> m :=
  match Nat.eq_dec n m with
  | right p => fun _ => p
  | left h => fun nh => False_rect _ (nh h)
  end.

Definition compute_le {n m} : n <= m -> n <= m :=
  match le_dec n m with
  | left p => fun _ => p
  | right nh => fun h => False_rect _ (nh h)
  end.

Definition compute_lt {n m} : n < m -> n < m :=
  match lt_dec n m with
  | left p => fun _ => p
  | right nh => fun h => False_rect _ (nh h)
  end.

Definition compute_ge {n m} : n >= m -> n >= m :=
  match ge_dec n m with
  | left p => fun _ => p
  | right nh => fun h => False_rect _ (nh h)
  end.

Definition compute_gt {n m} : n > m -> n > m :=
  match gt_dec n m with
  | left p => fun _ => p
  | right nh => fun h => False_rect _ (nh h)
  end.

Ltac mylia :=
  match goal with
  | |- @eq nat _ _ => eapply compute_eq ; abstract lia
  | |- _ <= _ => eapply compute_le ; abstract lia
  | |- _ < _ => eapply compute_lt ; abstract lia
  | |- _ >= _ => eapply compute_ge ; abstract lia
  | |- _ > _ => eapply compute_gt ; abstract lia
  | _ => abstract lia
  end.

Record pp_sigT {A : Type} (P : A -> Type) : Type :=
  {
    pi1 : A;
    pi2 : P pi1
  }.

Arguments pi1 {_ _} _.
Arguments pi2 {_ _} _.

(* Preamble *)
Notation "'∑'  x .. y , P" := (pp_sigT (fun x => .. (pp_sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Arguments Build_pp_sigT {_ _} _ _.

Notation "( x ; .. ; y ; z )" :=
  (Build_pp_sigT x (.. (Build_pp_sigT y z) ..)) : type_scope.

Record pp_prod (A B : Type) : Type := mk_pp_prod
  {
    pi1_ : A;
    pi2_ : B
  }.

Arguments mk_pp_prod {_ _} _ _.
Arguments pi1_ {_ _} _.
Arguments pi2_ {_ _} _.


Notation "x * y" := (pp_prod x y) : type_scope.

Definition fst {A B} (p : A * B) := pi1_ p.
Definition snd {A B} (p : A * B) := pi2_ p.

Notation "( x , y , .. , z )" :=
  (mk_pp_prod .. (mk_pp_prod x y) .. z) : type_scope.



Ltac splits n :=
  match n with
  | S ?n => split ; [ splits n |]
  | _ => idtac
  end.

Ltac split_hyp :=
  match goal with
  | H : _ * _ |- _ => destruct H
  end.

Ltac split_hyps :=
  repeat split_hyp.

Ltac splits_one h :=
  match type of h with
  | _ * _ => let h1 := fresh "h" in
            let h2 := fresh "h" in
            destruct h as [h1 h2] ;
            splits_one h1 ;
            splits_one h2
  | _ /\ _ => let h1 := fresh "h" in
            let h2 := fresh "h" in
            destruct h as [h1 h2] ;
            splits_one h1 ;
            splits_one h2
  | _ => idtac
  end.

Ltac bprop' H H' :=
  match type of H with
  | (?n <=? ?m) = true => pose proof (compute_le (leb_complete _ _ H)) as H'
  | (?n <=? ?m) = false => pose proof (compute_lt (leb_complete_conv _ _ H)) as H'
  | (?n <? ?m) = true => pose proof (compute_lt (proj1 (Nat.ltb_lt n m) H)) as H'
  | (?n <? ?m) = false => pose proof (compute_le (proj1 (Nat.ltb_ge n m) H)) as H'
  | (?x ?= ?y) = Gt => pose proof (compute_gt (nat_compare_Gt_gt _ _ H)) as H'
  | (?x ?= ?y) = Eq => pose proof (compute_eq (Nat.compare_eq _ _ H)) as H'
  | (?x ?= ?y) = Lt => pose proof (compute_lt (nat_compare_Lt_lt _ _ H)) as H'
  | (?x =? ?y) = true => pose proof (compute_eq (EqNat.beq_nat_true_stt x y H)) as H'
  | (?x =? ?y) = false => pose proof (compute_neq (EqNat.beq_nat_false_stt x y H)) as H'
  end.

(* Doesn't work. :( *)
Tactic Notation "brop" constr(H) "as" constr(H') := bprop' H H'.

Tactic Notation "bprop" constr(H) := let H' := fresh H in bprop' H  H'.

Definition compute_leb_true {n m} : n <=? m = true -> n <=? m = true :=
  match n <=? m with
  | true => fun _ => eq_refl
  | false => fun h => h
  end.

Definition compute_leb_false {n m} : n <=? m = false -> n <=? m = false :=
  match n <=? m with
  | false => fun _ => eq_refl
  | true => fun h => h
  end.

Definition compute_ltb_true {n m} : n <? m = true -> n <? m = true :=
  match n <? m with
  | true => fun _ => eq_refl
  | false => fun h => h
  end.

Definition compute_ltb_false {n m} : n <? m = false -> n <? m = false :=
  match n <? m with
  | false => fun _ => eq_refl
  | true => fun h => h
  end.

Definition compute_eqb_true {n m} : n =? m = true -> n =? m = true :=
  match n =? m with
  | true => fun _ => eq_refl
  | false => fun h => h
  end.

Definition compute_eqb_false {n m} : n =? m = false -> n =? m = false :=
  match n =? m with
  | false => fun _ => eq_refl
  | true => fun h => h
  end.

Definition compute_compare_Lt {n m} : n ?= m = Lt -> n ?= m = Lt :=
  match n ?= m with
  | Lt => fun _ => eq_refl
  | Eq => fun h => h
  | Gt => fun h => h
  end.

Definition compute_compare_Eq {n m} : n ?= m = Eq -> n ?= m = Eq :=
  match n ?= m with
  | Eq => fun _ => eq_refl
  | Lt => fun h => h
  | Gt => fun h => h
  end.

Definition compute_compare_Gt {n m} : n ?= m = Gt -> n ?= m = Gt :=
  match n ?= m with
  | Gt => fun _ => eq_refl
  | Lt => fun h => h
  | Eq => fun h => h
  end.

Ltac propb :=
  match goal with
  | |- (_ <=? _) = true => apply compute_leb_true ; apply leb_correct
  | |- (_ <=? _) = false => apply compute_leb_false ; apply leb_correct_conv
  | |- (_ <? _) = true => apply compute_ltb_true ; apply Nat.ltb_lt
  | |- (_ <? _) = false => apply compute_ltb_false ; apply Nat.ltb_ge
  | |- (_ ?= _) = Lt => apply compute_compare_Lt ; apply Nat.compare_lt_iff
  | |- (_ ?= _) = Eq => apply compute_compare_Eq ; apply Nat.compare_eq_iff
  | |- (_ ?= _) = Gt => apply compute_compare_Gt ; apply Nat.compare_gt_iff
  | |- (_ =? _) = true => apply compute_eqb_true ; apply Nat.eqb_eq
  | |- (_ =? _) = false => apply compute_eqb_false ; apply Nat.eqb_neq
  end.

(* Replace the opaque version *)
Fact andb_prop : forall a b, a && b = true -> a = true /\ b = true.
Proof.
  intros [] [] h.
  all: simpl in h.
  all: split ; (reflexivity + assumption).
Defined.

Ltac destruct_andb :=
  match goal with
  | H : _ && _ = true |- _ =>
    destruct (andb_prop _ _ H) ; clear H
  end.




Ltac rewrite_assumption :=
  match goal with
  | H : _, e : _ = _ |- _ => rewrite H
  | H : _ = _ |- _ => rewrite H
  end.

Ltac rewrite_assumptions :=
  repeat rewrite_assumption.

Ltac erewrite_assumption :=
  match goal with
  | H : _, e : _ = _ |- _ => erewrite H
  | H : _ = _ |- _ => erewrite H
  end.

Ltac erewrite_assumptions :=
  erewrite_assumption ; [ try erewrite_assumptions | .. ].

Tactic Notation "erewrite_assumption" "by" tactic(tac) :=
  match goal with
  | H : _, e : _ = _ |- _ => erewrite H by tac
  end.



Ltac ncase exp :=
  let e := fresh "e" in
  case_eq exp ; intro e ; bprop e ; try mylia.

Ltac nat_case :=
  match goal with
  | |- context [ ?n <=? ?m ] => ncase (n <=? m)
  | |- context [ ?n <? ?m ] => ncase (n <? m)
  | |- context [ ?n =? ?m ] => ncase (n =? m)
  | |- context [ ?n ?= ?m ] => ncase (n ?= m)
  end.

Tactic Notation "hyp" "rewrite" :=
  match goal with
  | H : _ |- _ => rewrite H by mylia
  end.




Definition rev {A} (l : list A) : list A :=
  let fix aux (l : list A) (acc : list A) : list A :=
    match l with
    | [] => acc
    | x :: l => aux l (x :: acc)
    end
  in aux l [].

Definition rev_map {A B} (f : A -> B) (l : list A) : list B :=
  let fix aux (l : list A) (acc : list B) : list B :=
    match l with
    | [] => acc
    | x :: l => aux l (f x :: acc)
    end
  in aux l [].

Notation "#| Γ |" := (List.length Γ) (at level 0, Γ at level 99, format "#| Γ |").


Fact skipn_all :
  forall {A} {l : list A},
    skipn #|l| l = [].
Proof.
  intros A l. induction l.
  - cbn. reflexivity.
  - cbn. assumption.
Defined.

Fact skipn_length :
  forall {A} {l : list A} {n},
    #|skipn n l| = #|l| - n.
Proof.
  intros A. induction l ; intro n.
  - cbn. destruct n ; reflexivity.
  - destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Defined.

Fact skipn_reconstruct :
  forall {A} {l : list A} {n a},
    nth_error l n = Some a ->
    skipn n l = a :: skipn (S n) l.
Proof.
  intros A l.
  induction l ; intros n x hn.
  - destruct n ; cbn in hn ; inversion hn.
  - cbn. destruct n.
    + cbn. cbn in hn. inversion hn. reflexivity.
    + apply IHl. now inversion hn.
Defined.

Fact firstn_reconstruct :
  forall {A} {l : list A} {n a},
    nth_error l n = Some a ->
    firstn (S n) l = (firstn n l ++ [a])%list.
Proof.
  intros A l.
  induction l ; intros n x hn.
  - destruct n ; cbn in hn ; inversion hn.
  - cbn. destruct n.
    + cbn. cbn in hn. inversion hn. reflexivity.
    + inversion hn as [e].
      erewrite IHl by exact e. cbn. reflexivity.
Defined.

Definition lastn n {A} (l : list A) :=
  skipn (#|l| - n) l.

Fact lastn_O :
  forall {A} {l : list A}, lastn 0 l = [].
Proof.
  intros A l. unfold lastn.
  replace (#|l| - 0) with #|l| by mylia.
  apply skipn_all.
Defined.

Fact lastn_all :
  forall {A} {l : list A},
    lastn #|l| l = l.
Proof.
  intros A l. unfold lastn.
  replace (#|l| - #|l|) with 0 by mylia.
  reflexivity.
Defined.

Fact lastn_all2 :
  forall {A} {n} {l : list A},
    #|l| <= n ->
    lastn n l = l.
Proof.
  intros A n l h.
  unfold lastn.
  replace (#|l| - n) with 0 by mylia.
  reflexivity.
Defined.

Fact lastn_reconstruct :
  forall {A} {l : list A} {n a},
    nth_error l (#|l| - S n) = Some a ->
    n < #|l| ->
    lastn (S n) l = a :: lastn n l.
Proof.
  intros A l n a hn h.
  unfold lastn.
  erewrite skipn_reconstruct.
  - f_equal. f_equal. mylia.
  - assumption.
Defined.

Fact map_firstn :
  forall {A} {l1 l2 : list A} {B} {f : A -> B} {n},
    map f l1 = map f l2 ->
    map f (firstn n l1) = map f (firstn n l2).
Proof.
  intros A l1 l2 B f n h. revert l2 n h.
  induction l1 ; intros l2 n h ; destruct l2 ; cbn in h ; try discriminate h.
  - reflexivity.
  - destruct n.
    + cbn. reflexivity.
    + inversion h.
      cbn. f_equal ; try assumption.
      apply IHl1. assumption.
Defined.

Fact map_skipn :
  forall {A} {l1 l2 : list A} {B} {f : A -> B} {n},
    map f l1 = map f l2 ->
    map f (skipn n l1) = map f (skipn n l2).
Proof.
  intros A l1 l2 B f n h. revert l2 n h.
  induction l1 ; intros l2 n h ; destruct l2 ; cbn in h ; try discriminate h.
  - reflexivity.
  - inversion h.
    destruct n.
    + cbn. f_equal ; assumption.
    + cbn. eapply IHl1. assumption.
Defined.

Definition dec (A : Type) := A + { A -> False }.



(* Associative table indexed by strings *)
Inductive assoc (A : Type) :=
| empty
| acons (key : string) (data : A) (t : assoc A).

Arguments empty {_}.
Arguments acons {_} _ _.

Fixpoint assoc_at {A} (key : string) (t : assoc A) {struct t} : option A :=
  match t with
  | empty => None
  | acons k a r => if string_dec key k then Some a else assoc_at key r
  end.



Definition ident := string.

Definition ident_eq (x y : ident) :=
  match string_dec x y with
  | left _ => true
  | right _ => false
  end.

Lemma nth_error_isdecl {A} {l : list A} {n c} :
  forall e : nth_error l n = Some c, n < #|l|.
Proof.
  revert l. induction n.
  destruct l; cbn. discriminate. intro; lia.
  destruct l; cbn. discriminate. intro H; apply IHn in H; lia.
Defined.

Lemma nth_error_Some_length :
  forall A (l : list A) n x,
    nth_error l n = Some x ->
    n < #|l|.
Proof.
  intros A l n x e.
  apply nth_error_Some.
  rewrite e. discriminate.
Qed.




Ltac easy := Coq.Init.Tactics.easy || solve [eauto 4 with core arith].
Tactic Notation "now" tactic(t) := t; easy.
