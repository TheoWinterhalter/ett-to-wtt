From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From Equations Require Import Equations.
From Translation Require Import util WAst.
From Translation Require Sorts.

Open Scope type_scope.

Fixpoint lift `{Sort_notion : Sorts.notion} n k t : wterm :=
  match t with
  | wRel i => if Nat.leb k i then wRel (n + i) else wRel i
  | wLambda T M => wLambda (lift n k T) (lift n (S k) M)
  | wApp u v => wApp (lift n k u) (lift n k v)
  | wProd A B => wProd (lift n k A) (lift n (S k) B)
  | wSum A B => wSum (lift n k A) (lift n (S k) B)
  | wPair A B u v =>
    wPair (lift n k A) (lift n (S k) B) (lift n k u) (lift n k v)
  | wPi1 A B p => wPi1 (lift n k A) (lift n (S k) B) (lift n k p)
  | wPi2 A B p => wPi2 (lift n k A) (lift n (S k) B) (lift n k p)
  | wEq A u v => wEq (lift n k A) (lift n k u) (lift n k v)
  | wRefl A u => wRefl (lift n k A) (lift n k u)
  | wJ A u P w v p =>
    wJ (lift n k A)
       (lift n k u)
       (lift n (S (S k)) P)
       (lift n k w)
       (lift n k v)
       (lift n k p)
  | wTransport A B p t =>
    wTransport (lift n k A) (lift n k B) (lift n k p) (lift n k t)
  | wBeta t u => wBeta (lift n (S k) t) (lift n k u)
  | wK A u p => wK (lift n k A) (lift n k u) (lift n k p)
  | wFunext f g p => wFunext (lift n k f) (lift n k g) (lift n k p)
  | wJBeta u P w => wJBeta (lift n k u) (lift n (S (S k)) P) (lift n k w)
  | wTransportBeta A u => wTransportBeta (lift n k A) (lift n k u)
  | wPairEta p => wPairEta (lift n k p)
  | wProdExt A p => wProdExt (lift n k A) (lift n (S k) p)
  | wSumExt A p => wSumExt (lift n k A) (lift n (S k) p)
  | wSort s => wSort s
  | wAx id => wAx id
  | wDelta id => wDelta id
  end.

Notation lift0 n t := (lift n 0 t).
Notation "↑" := (lift 1 0).

Fixpoint subst `{Sort_notion : Sorts.notion} t k u :=
  match u with
  | wRel n =>
    match k ?= n with
    | Datatypes.Eq => lift0 k t
    | Gt => wRel n
    | Lt => wRel (pred n)
    end
  | wLambda T M => wLambda (subst t k T) (subst t (S k) M)
  | wApp u v => wApp (subst t k u) (subst t k v)
  | wProd A B => wProd (subst t k A) (subst t (S k) B)
  | wSum A B => wSum (subst t k A) (subst t (S k) B)
  | wPair A B u v =>
    wPair (subst t k A) (subst t (S k) B) (subst t k u) (subst t k v)
  | wPi1 A B p => wPi1 (subst t k A) (subst t (S k) B) (subst t k p)
  | wPi2 A B p => wPi2 (subst t k A) (subst t (S k) B) (subst t k p)
  | wEq A u v => wEq (subst t k A) (subst t k u) (subst t k v)
  | wRefl A u => wRefl (subst t k A) (subst t k u)
  | wJ A u P w v p =>
    wJ (subst t k A)
       (subst t k u)
       (subst t (S (S k)) P)
       (subst t k w)
       (subst t k v)
       (subst t k p)
  | wTransport A B p u =>
    wTransport (subst t k A) (subst t k B) (subst t k p) (subst t k u)
  | wBeta f u => wBeta (subst t (S k) f) (subst t k u)
  | wK A u p => wK (subst t k A) (subst t k u) (subst t k p)
  | wFunext f g p => wFunext (subst t k f) (subst t k g) (subst t k p)
  | wJBeta u P w => wJBeta (subst t k u) (subst t (S (S k)) P) (subst t k w)
  | wTransportBeta A u => wTransportBeta (subst t k A) (subst t k u)
  | wPairEta p => wPairEta (subst t k p)
  | wProdExt A p => wProdExt (subst t k A) (subst t (S k) p)
  | wSumExt A p => wSumExt (subst t k A) (subst t (S k) p)
  | wSort s => wSort s
  | wAx id => wAx id
  | wDelta id => wDelta id
  end.

Declare Scope w_scope.

Notation subst0 t u := (subst t 0 u).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity) : w_scope.

Open Scope w_scope.

Section LiftSubst.

Context `{Sort_notion : Sorts.notion}.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)]*)
Definition substl l t :=
  List.fold_left (fun t u => subst0 u t) l t.

(* Notion of closedness *)
Fixpoint closed_above k (t : wterm) :=
  match t with
  | wRel n => n <? k
  | wSort _ => true
  | wProd A B => closed_above k A && closed_above (S k) B
  | wLambda A t => closed_above k A && closed_above (S k) t
  | wApp u v => closed_above k u && closed_above k v
  | wSum A B => closed_above k A && closed_above (S k) B
  | wPair A B u v =>
    closed_above k A && closed_above (S k) B &&
    closed_above k u && closed_above k v
  | wPi1 A B p => closed_above k A && closed_above (S k) B && closed_above k p
  | wPi2 A B p => closed_above k A && closed_above (S k) B && closed_above k p
  | wEq A u v =>
    closed_above k A && closed_above k u && closed_above k v
  | wRefl A u =>
    closed_above k A && closed_above k u
  | wJ A u P w v p =>
    closed_above k A &&
    closed_above k u &&
    closed_above (S (S k)) P &&
    closed_above k w &&
    closed_above k v &&
    closed_above k p
  | wTransport A B p u =>
    closed_above k A &&
    closed_above k B &&
    closed_above k p &&
    closed_above k u
  | wBeta t u =>
    closed_above (S k) t &&
    closed_above k u
  | wK A u p =>
    closed_above k A &&
    closed_above k u &&
    closed_above k p
  | wFunext f g p =>
    closed_above k f &&
    closed_above k g &&
    closed_above k p
  | wJBeta u P w =>
    closed_above k u &&
    closed_above (S (S k)) P &&
    closed_above k w
  | wTransportBeta A t =>
    closed_above k A &&
    closed_above k t
  | wPairEta p => closed_above k p
  | wProdExt A p => closed_above k A && closed_above (S k) p
  | wSumExt A p => closed_above k A && closed_above (S k) p
  | wAx id => true
  | wDelta id => true
  end.

Definition closed t := closed_above 0 t = true.

(* Lemmata regarding lifts and subst *)

Lemma lift_lift :
  forall t n m k,
    lift n k (lift m k t) = lift (n+m) k t.
Proof.
  intros t.
  induction t ; intros nn mm kk.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case.
    f_equal. mylia.
  - cbn. rewrite e. reflexivity.
Defined.

Lemma liftP1 :
  forall t i j k, lift k (j+i) (lift j i t) = lift (j+k) i t.
Proof.
  intro t.
  induction t ; intros i j k.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j+i))))%nat with (j + (S (S (S i))))%nat by mylia ;
            try replace (S (S (j+i)))%nat with (j + (S (S i)))%nat by mylia ;
            try replace (S (j+i))%nat with (j + (S i))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case.
    f_equal. mylia.
  - cbn. nat_case.
    reflexivity.
Defined.

Lemma liftP2 :
  forall t i j k n,
    i <= n ->
    lift k (j+n) (lift j i t) = lift j i (lift k n t).
Proof.
  intro t.
  induction t ; intros i j k m H.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by mylia ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by mylia ;
            try replace (S (j + m))%nat with (j + (S m))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - nat_case.
    + cbn. nat_case. nat_case.
      f_equal. mylia.
    + cbn. nat_case. nat_case.
      reflexivity.
  - cbn. nat_case. nat_case.
    cbn. nat_case. reflexivity.
Defined.

Lemma lift_subst :
  forall {t n u},
    (lift 1 n t) {n := u} = t.
Proof.
  intro t.
  induction t ; intros m u.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case. reflexivity.
  - cbn. nat_case. reflexivity.
Defined.

Lemma lift00 :
  forall {t n}, lift 0 n t = t.
Proof.
  intros t. induction t ; intro m.
  all: cbn.
  all: repeat match goal with
           | H : forall n, _ = _ |- _ => rewrite H
           end.
  all: try reflexivity.
  destruct (m <=? n) ; reflexivity.
Defined.

Lemma liftP3 :
  forall t i k j n,
    i <= k ->
    k <= (i+n)%nat ->
    lift j k (lift n i t) = lift (j+n) i t.
Proof.
  intro t. induction t ; intros i k j m ilk kl.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case. f_equal. mylia.
  - cbn. nat_case. reflexivity.
Defined.

Lemma substP1 :
  forall t u i j k,
    lift k (j+i) (t{j := u}) = (lift k (S (j+i)) t){ j := lift k i u }.
Proof.
  intro t. induction t ; intros u i j k.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + i)))) with ((S (S (S j))) + i)%nat by mylia ;
            try replace (S (S (j + i))) with ((S (S j)) + i)%nat by mylia ;
            try replace (S (j + i)) with ((S j) + i)%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn - [Nat.leb]. nat_case.
  - cbn. nat_case. cbn. nat_case.
    nat_case. f_equal. mylia.
  - cbn. nat_case.
    + subst. apply liftP2. mylia.
    + cbn. nat_case. reflexivity.
    + cbn. nat_case. reflexivity.
Defined.

Lemma substP2 :
  forall t u i j n,
    i <= n ->
    (lift j i t){ (j+n)%nat := u } = lift j i (t{ n := u }).
Proof.
  intros t.
  induction t ; intros u i j m h.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by mylia ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by mylia ;
            try replace (S (j + m))%nat with (j + (S m))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case.
    + nat_case. subst. rewrite liftP3 by mylia. reflexivity.
    + nat_case. cbn. nat_case. f_equal. mylia.
    + nat_case. cbn. nat_case. reflexivity.
  - cbn. nat_case. nat_case. cbn. nat_case. reflexivity.
Defined.

Lemma substP3 :
  forall t u i k n,
    i <= k ->
    k <= i + n ->
    (lift (S n) i t){ k := u } = lift n i t.
Proof.
  intro t. induction t ; intros u i k m ilk kls.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by mylia ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by mylia ;
            try replace (S (j + m))%nat with (j + (S m))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case. reflexivity.
  - cbn. nat_case. reflexivity.
Defined.

Lemma substP4 :
  forall t u v i j,
    t{ i := u }{ i+j := v } = t{ S (i+j) := v}{ i := u{ j := v } }.
Proof.
  intro t ; induction t ; intros u v i j.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (i + j))))%nat with ((S (S (S i))) + j)%nat by mylia ;
            try replace (S (S (i + j)))%nat with ((S (S i)) + j)%nat by mylia ;
            try replace (S (i + j))%nat with ((S i) + j)%nat by mylia ;
            hyp rewrite ; reflexivity
           ).
  cbn - [Nat.compare]. nat_case.
  - subst. nat_case. cbn. nat_case.
    rewrite substP2 by mylia. reflexivity.
  - cbn - [Nat.compare]. nat_case.
    + nat_case. rewrite substP3 by mylia. reflexivity.
    + nat_case. cbn. nat_case. reflexivity.
    + nat_case. cbn. nat_case. reflexivity.
  - cbn - [Nat.compare]. nat_case.
    nat_case. cbn. nat_case. reflexivity.
Defined.

Ltac erewrite_close_above_lift :=
  match goal with
  | H : forall n k l, k <= l -> _ = _ |- _ =>
    erewrite H by mylia
  end.

Lemma closed_above_lift :
  forall {t n k l},
    k <= l ->
    closed_above (n+l) (lift n k t) =
    closed_above l t.
Proof.
  intro t. induction t ; intros m k l h.
  all: try (cbn ;
            try replace (S (S (m+l)))%nat with (m + S (S l))%nat by mylia ;
            try replace (S (m+l))%nat with (m + S l)%nat by mylia ;
            repeat erewrite_close_above_lift ;
            reflexivity).
  unfold lift. nat_case.
  - unfold closed_above.
    nat_case.
    + nat_case.
    + nat_case.
  - unfold closed_above. nat_case. nat_case.
Defined.

Ltac erewrite_close_above_lift_id :=
  match goal with
  | H : forall n k l, _ -> k >= l -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.

Fact closed_above_lift_id :
  forall t n k l,
    closed_above l t = true ->
    k >= l ->
    lift n k t = t.
Proof.
  intro t. induction t ; intros m k l clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_lift_id ;
            reflexivity).
  unfold closed in clo. unfold closed_above in clo.
  bprop clo. cbn. nat_case. reflexivity.
Defined.

Fact closed_lift :
  forall t n k,
    closed t ->
    lift n k t = t.
Proof.
  intros t n k h.
  unfold closed in h.
  eapply closed_above_lift_id.
  - eassumption.
  - mylia.
Defined.

Ltac erewrite_close_above_subst :=
  match goal with
  | H : forall u l n, _ -> _ -> _ -> _ = _ |- _ =>
    erewrite H by (mylia || reflexivity || assumption)
  end.

Lemma closed_above_subst :
  forall {t u l n},
    n <= l ->
    closed_above (S l) t = true ->
    closed_above (l - n) u = true ->
    closed_above l (t{ n := u }) = true.
Proof.
  intro t. induction t ; intros u l m h0 h1 h2.
  all: try (cbn ; cbn in h1 ; repeat destruct_andb ;
            repeat erewrite_close_above_subst ; reflexivity).
  unfold closed_above in h1. bprop h1.
  cbn. nat_case.
  + subst. replace l with (n + (l - n))%nat by mylia.
    rewrite closed_above_lift by mylia. assumption.
  + unfold closed_above. nat_case.
  + unfold closed_above. nat_case.
Defined.

Ltac erewrite_close_above_subst_id :=
  match goal with
  | H : forall n l u, _ -> _ -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.

Fact closed_above_subst_id :
  forall t n l u,
    closed_above l t = true ->
    n >= l ->
    t{ n := u } = t.
Proof.
  intro t. induction t ; intros m l u clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_subst_id ;
            reflexivity).
  unfold closed in clo. unfold closed_above in clo.
  bprop clo. cbn. nat_case. reflexivity.
Defined.

Fact closed_subst :
  forall t n u,
    closed t ->
    t{ n := u } = t.
Proof.
  intros t n u h.
  unfold closed in h.
  eapply closed_above_subst_id.
  - eassumption.
  - mylia.
Defined.

End LiftSubst.

(* Exporting the tactics that were defined inside the section. *)

Ltac erewrite_close_above_lift :=
  match goal with
  | H : forall n k l, k <= l -> _ = _ |- _ =>
    erewrite H by mylia
  end.

Ltac erewrite_close_above_lift_id :=
  match goal with
  | H : forall n k l, _ -> k >= l -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.

Ltac erewrite_close_above_subst :=
  match goal with
  | H : forall u l n, _ -> _ -> _ -> _ = _ |- _ =>
    erewrite H by (mylia || eassumption)
  end.

Ltac erewrite_close_above_subst_id :=
  match goal with
  | H : forall n l u, _ -> _ -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.