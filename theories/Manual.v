(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template
Require Import Ast utils monad_utils Typing Checker.
From Equations Require Import Equations DepElimDec.
From Translation
Require Import util Sorts WAst WEquality WLiftSubst WTyping WTypingInversions WChecker WLemmata Quotes.
From TypingFlags Require Import Loader.
Import MonadNotation ListNotations.

Notation "⇑ t" := (lift 1 0 t) (at level 3, format "'⇑' t").
Notation "A ↦ B" := (wProd nAnon A (↑ B)) (at level 30, right associativity).


Ltac gitt_as H XX :=
  simple refine (let XX := istype_type _ H in _);
  [try eassumption|
   let s := fresh "s" in destruct XX as [s XX]].

Tactic Notation "gitt" ident(H1) := let XX := fresh in gitt_as H1 XX.
Tactic Notation "gitt" ident(H1) ident(H2) := gitt H1; gitt H2.
Tactic Notation "gitt" ident(H1) ident(H2) ident(H3) := gitt H1; gitt H2; gitt H3.

Ltac inverse H :=
  lazymatch type of H with
  | _ ;;; _ |-w _ : wEq _ _ _ =>
    let XX := fresh "H" in
    gitt_as H XX;
    eapply inversion_Eq in XX;
    destruct XX as [?s [?H [?H [?H _]]]]
  | _ ;;; _ |-w _ : wProd _ _ _ =>
    let XX := fresh "H" in
    gitt_as H XX;
    eapply inversion_Prod in XX;
    destruct XX as [?s [?s [?H [?H _]]]]
  end.


Section Admissibles1.
  Context {S : notion} Σ (HΣ : type_glob Σ).

  Definition type_Lambda Γ n n' t A B :
      Σ ;;; Γ ,, A |-w t : B ->
      Σ ;;; Γ |-w wLambda n A t : wProd n' A B.
  Proof.
    intros H. pose proof (typing_wf H).
    inversion H0. now eapply type_Lambda.
  Defined.
   
  Definition type_Pair Γ n A B u v s2 :
      Σ ;;; Γ |-w u : A ->
      Σ;;; Γ,, A |-w B : wSort s2 ->
      Σ ;;; Γ |-w v : B{ 0 := u } ->
      Σ ;;; Γ |-w wPair A B u v : wSum n A B.
  Proof.
    intros Hu Hv. gitt Hu.
    econstructor; eassumption.
  Defined.
   
  Definition type_Pi1 Γ n A B p :
      Σ ;;; Γ |-w p : wSum n A B ->
      Σ ;;; Γ |-w wPi1 A B p : A.
  Proof.
    intro Hp; gitt Hp.
    apply inversion_Sum in H.
    destruct H as [s1 [s2 [H1 [H2 H3]]]].
    econstructor; eassumption.
  Defined.
   
  Definition type_Pi2 Γ n A B p :
      Σ ;;; Γ |-w p : wSum n A B ->
      Σ ;;; Γ |-w wPi2 A B p : B{ 0 := wPi1 A B p }.
  Proof.
    intro Hp; gitt Hp.
    apply inversion_Sum in H.
    destruct H as [s1 [s2 [H1 [H2 H3]]]].
    econstructor; eassumption.
  Defined.
   
  Definition type_Refl Γ A u :
      Σ ;;; Γ |-w u : A ->
      Σ ;;; Γ |-w wRefl A u : wEq A u u.
  Proof.
    intro Hp; gitt Hp.
    econstructor; eassumption.
  Defined.

  Definition type_J Γ s2 A u v P p w :
      Σ ;;; Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0)) |-w P : wSort s2 ->
      Σ ;;; Γ |-w p : wEq A u v ->
      Σ ;;; Γ |-w w : P{ 1 := u }{ 0 := wRefl A u } ->
      Σ ;;; Γ |-w wJ A u P w v p : P{ 1 := v }{ 0 := p }.
  Proof.
    intros HP Hp Hw. inverse Hp.
    econstructor; eassumption.
  Defined.
   
  Definition type_Beta Γ A B t u n :
      Σ ;;; Γ ,, A |-w t : B ->
      Σ ;;; Γ |-w u : A ->
      Σ ;;; Γ |-w wBeta t u : wEq (B{ 0 := u })
                                 (wApp (wLambda n A t) u)
                                 (t{ 0 := u }).
  Proof.
    intros Ht Hu. gitt Hu.
    econstructor; eassumption.
  Defined.
   
  Definition type_K Γ A u p :
      Σ;;; Γ |-w p : wEq A u u ->
      Σ ;;; Γ |-w wK A u p : wEq (wEq A u u) p (wRefl A u).
  Proof.
    intros Hp. inverse Hp.
    econstructor; eassumption.
  Defined.
   
  Definition type_JBeta Γ A u P w s2 :
      Σ ;;; Γ |-w u : A ->
      Σ ;;; Γ ,, A ,, (wEq (lift0 1 A) (lift0 1 u) (wRel 0)) |-w P : wSort s2 ->
      Σ ;;; Γ |-w w : P{ 1 := u }{ 0 := wRefl A u } ->
      Σ ;;; Γ |-w wJBeta u P w : wEq (P{ 1 := u }{ 0 := wRefl A u })
                                  (wJ A u P w u (wRefl A u)) w.
  Proof.
    intros Hu HP Hw. gitt Hu.
    econstructor; eassumption.
  Defined.


Open Scope w_scope.
(* todo reuse existing notation *)
Notation " Γ  ,,, Γ' " :=
  (wapp_context Γ Γ')
    (at level 25, Γ' at next level, left associativity) : w_scope.


Lemma inverse_lift t u n k
  : lift n k t = lift n k u -> t = u.
Proof.
  revert k u; induction t; intros k u; cbn.
  { case_eq (k <=? n0); intro eq.
    + destruct u; intros e; inversion e as [e']. revert e'.
      case_eq (k <=? n1); intro eq'. inversion 1.
      apply Nat.add_cancel_l in H0. now rewrite H0.
      inversion 1. subst.
      eapply leb_iff_conv in eq'.
      eapply leb_complete in eq. omega.
    + destruct u; intros e; inversion e as [e']. revert e'.
      case_eq (k <=? n1); intro eq'. inversion 1. subst.
      eapply leb_iff_conv in eq.
      eapply leb_complete in eq'. omega.
      easy.
  }
  all: destruct u; intros e; inversion e as [e'];
      try (destruct (k <=? n0); inversion e'); try reflexivity.
  all: try erewrite IHt by eassumption.
  all: try erewrite IHt1 by eassumption.
  all: try erewrite IHt2 by eassumption.
  all: try erewrite IHt3 by eassumption.
  all: try erewrite IHt4 by eassumption.
  all: try erewrite IHt5 by eassumption.
  all: try erewrite IHt6 by eassumption.
  all: try reflexivity.
Qed.

Fixpoint inversion_lift {Γ Δ Ξ t A}
  (h : Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-w lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A)
  {struct h} : Σ ;;; Γ ,,, Ξ |-w t : A
with inversion_lift_wf {Γ Δ Ξ}
  (h : wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)) {struct h} :
  wf Σ (Γ ,,, Ξ).
Proof.
  { dependent destruction h.
    - destruct t; inversion H1. clear H1.
      cbn in H0. admit.
    - destruct t; inversion H1. destruct (#|Ξ| <=? n); inversion H3.
      destruct A; inversion H0. destruct (#|Ξ| <=? n); inversion H4.
      now constructor.
    - destruct t; inversion H0. destruct (#|Ξ| <=? n0); inversion H2.
      destruct A; inversion H. destruct (#|Ξ| <=? n0); inversion H5.
      subst. constructor. easy. eapply inversion_lift with (Ξ := Ξ ,, t1).
      cbn; eassumption.
    - destruct t; inversion H0. destruct (#|Ξ| <=? n0); inversion H2.
      destruct A; inversion H. destruct (#|Ξ| <=? n0); inversion H5.
      subst. eapply inverse_lift in H6; rewrite H6.
      eapply type_Lambda. eapply inversion_lift with (Ξ := Ξ ,, t1).
      cbn; eassumption.
    - destruct t; inversion H0. destruct (#|Ξ| <=? n0); inversion H2.
Admitted.

Corollary inversion_lift01 :
  forall {Γ t A B},
    Σ ;;; Γ ,, B |-w lift0 1 t : lift0 1 A ->
    Σ ;;; Γ |-w t : A.
Proof.
  intros Γ t A B H. 
  apply (@inversion_lift _ [ B ] nil). eassumption.
Defined.

End Admissibles1.

Definition type_glob_cons {S : notion} Σ d :
                     type_glob Σ ->
                     fresh_glob (dname d) Σ ->
                     Σ;;; [] |-w dbody d : dtype d -> type_glob (d :: Σ).
Proof.
  econstructor; try eassumption.
  eapply istype_type; eassumption.
Defined.


Ltac other_ittintro t := fail "No introduction rule for" t.

Ltac ittintro :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-w ?t : ?T =>
    lazymatch t with
    | wRel ?n => refine (type_Rel _ _ n _ _)
    | wSort _ => eapply type_Sort
    | wProd _ _ _ => eapply type_Prod
    | wLambda _ _ _ => eapply type_Lambda
    | wApp _ _ => eapply type_App
    | wSum _ _ _ => eapply type_Sum
    | wPair _ _ _ _ => eapply type_Pair
    | wPi1 _ _ _ => eapply type_Pi1
    | wPi2 _ _ _ => eapply type_Pi2
    | wEq _ _ _ => eapply type_Eq
    | wRefl _ _ => eapply type_Refl
    | wJ _ _ _ _ _ _ => eapply type_J
    | wBeta _ _ => eapply type_Beta
    | wK _ _ _ => eapply type_K
    | wFunext _ _ _ => eapply type_Funext
    | wJBeta _ _ _ => eapply type_JBeta
    | wPairEta _ => eapply type_PairEta
    | wAx _ => eapply type_Ax ; [| try reflexivity ]
    | wDelta _ => eapply type_Ax ; [| try reflexivity ]
    | _ => other_ittintro t
    end
  | _ => fail "Not applicable"
  end.

Ltac glob Σ:=
  first [
    eapply type_glob_nil
  | eapply type_glob_cons ; [
      idtac
    | repeat (lazy ; econstructor) ; lazy ; try discriminate
    | (* repeat econstructor *)
    ]
  ].

Ltac ittcheck1 :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-w ?t : ?T =>
    match goal with
    | |- _ => eassumption
    | |- _ => ittintro
    | |- _ => eapply meta_conv; [ittintro| try reflexivity]
    | |- ?Σ ;;; ?Γ |-w ↑ ?t : ?T => eapply meta_conv; [eapply typing_lift01|]
    | |- ?Σ ;;; ?Γ |-w lift0 2 ?t : ?T => eapply meta_conv; [eapply typing_lift02|]
    | |- ?Σ ;;; ?Γ |-w lift0 3 ?t : ?T => eapply meta_conv; [eapply typing_lift03|]
    | |- ?Σ ;;; ?Γ |-w lift0 4 ?t : ?T => eapply meta_conv; [eapply typing_lift04|]
    | HH : ?Σ ;;; ?Γ |-w ?t : _ |- _ ;;; _ |-w ?t : _ =>
      eapply meta_conv; [eapply HH|]
    end
  | |- wf ?Σ ?Γ => first [ assumption | econstructor ]
  | |- _ = _ => first [ simpl; reflexivity | now rewrite !lift_lift (* wrong if evars *) | shelve ]
  | |- type_glob _ => first [ assumption | glob ]
  | _ => fail "Not applicable"
  end.

Ltac substP3 := rewrite !substP3, ?lift00 by omega; try reflexivity.

Ltac ittcheck := repeat (ittcheck1 ; try (lazy ; myomega)).

(* Ltac use id := eapply meta_conv; [eapply id | try reflexivity]; ittcheck. *)

Section Manual.
  Context {S : notion} Σ (HΣ : type_glob Σ).


Notation "'exists' x .. y , p" := (pp_sigT (fun x => .. (pp_sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition wtransport A P x y e u := wJ A x (↑ P) u y e.

Definition type_transport Γ A P x y e u s' :
      wf Σ Γ ->
      Σ ;;; Γ ,, A |-w P : wSort s' ->
      Σ ;;; Γ |-w e : wEq A x y ->
      Σ ;;; Γ |-w u : P {0 := x} ->
      Σ ;;; Γ |-w wtransport  A P x y e u : P {0 := y}.
Proof.
  intros HΓ HP He Hu; unfold wtransport.
  inverse He. ittcheck.
  Unshelve.
  rewrite (substP2 P x 0 1 0) by omega.
  substP3.
  rewrite (substP2 P y 0 1 0) by omega.
  substP3.
Defined.

Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | _ => fail "No introduction rule for" t
  end.


Definition wcoe s A B p x := wtransport (wSort s) (wRel 0) A B p x.

Definition type_coe Γ s A B p x :
      wf Σ Γ ->
      Σ ;;; Γ |-w p : wEq (wSort s) A B ->
      Σ ;;; Γ |-w x : A ->
      Σ ;;; Γ |-w wcoe s A B p x : B.
Proof.
  intros HΓ Hp Hx; unfold wcoe.
  inverse Hp. ittcheck.
  Unshelve. 
  all: cbn; now rewrite lift00.
Defined.

Definition lift_coe s A B p x n k
  : lift n k (wcoe s A B p x)
    = wcoe s (lift n k A) (lift n k B) (lift n k p) (lift n k x).
Proof.
  reflexivity.
Defined.

Definition subst_coe s A B p x n t
  : (wcoe s A B p x){n := t}
    = wcoe s (A{n := t}) (B{n := t}) (p{n := t}) (x{n := t}).
Proof.
  reflexivity.
Defined.

Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | _ => fail "No introduction rule for" t
  end.


Definition wHeq s A a B b :=
  wSum (nNamed "e") (wEq (wSort s) A B)
       (wEq (↑ B) (wcoe s (↑ A) (↑ B) (wRel 0) (↑ a)) (↑ b)).

Notation "'heq_sort' s" :=
  (sum_sort (eq_sort (succ s)) (eq_sort s)) (at level 30).

Definition type_heq Γ s A a B b :
      wf Σ Γ ->
      Σ ;;; Γ |-w A : wSort s ->
      Σ ;;; Γ |-w B : wSort s ->
      Σ ;;; Γ |-w a : A ->
      Σ ;;; Γ |-w b : B ->
      Σ ;;; Γ |-w wHeq s A a B b : wSort (heq_sort s).
Proof.
  intros HΓ HA HB Ha Hb; unfold wHeq.
  ittcheck.
Defined.

Definition lift_heq s A a B b n k
  : lift n k (wHeq s A a B b)
    = wHeq s (lift n k A) (lift n k a) (lift n k B) (lift n k b).
Proof.
  unfold wHeq; cbn -[wcoe].
  rewrite lift_coe.
  rewrite !(liftP2 _ 0 1) by omega. reflexivity.
Defined.

Definition subst_heq s A a B b n t
  : (wHeq s A a B b){n := t}
    = wHeq s (A{n := t}) (a{n := t}) (B{n := t}) (b{n := t}).
Proof.
  unfold wHeq; cbn -[wcoe].
  rewrite <- !substP2 by omega. cbn -[wcoe].
  rewrite subst_coe. reflexivity.
Defined.


Lemma inversion_Heq :
  forall {Γ A B a b T s},
    Σ ;;; Γ |-w wHeq s A a B b : T ->
      Σ ;;; Γ |-w A : wSort s /\
      Σ ;;; Γ |-w a : A /\
      Σ ;;; Γ |-w B : wSort s /\
      Σ ;;; Γ |-w b : B /\
      nl T = nlSort (heq_sort s).
Proof.
  intros Γ A B a b T s H. unfold wHeq in H.
  eapply inversion_Sum in H. destruct H as [s1 [s2 [H1 [H2 eq]]]].
  eapply inversion_Eq in H1. destruct H1 as [s' [H1 [H1' [H1'' eq']]]].
  eapply inversion_Eq in H2. destruct H2 as [s'' [H2 [H2' [H2'' eq'']]]].
  cbn in *. inversion eq'; inversion eq''; subst.
  unfold wcoe, wtransport in H2'.
  eapply inversionJ in H2'.
  destruct H2' as [s1 [s2 [H3 [H3' [H3'' [H33 [H34 [H35 eq3]]]]]]]].
  repeat split ; try eassumption.
  - clear - H35 HΣ. cbn in H35. rewrite substP3, lift00 in H35 by omega.
    eapply inversion_lift01; eassumption.
  - eapply inversion_lift01; eassumption.
  - etransitivity. eassumption.
    admit.
Admitted.

Ltac inverse H ::=
  lazymatch type of H with
  | _ ;;; _ |-w _ : wEq _ _ _ =>
    let XX := fresh "H" in
    gitt_as H XX;
    eapply inversion_Eq in XX;
    destruct XX as [?s [?H [?H [?H _]]]]
  | _ ;;; _ |-w _ : wProd _ _ _ =>
    let XX := fresh "H" in
    gitt_as H XX;
    eapply inversion_Prod in XX;
    destruct XX as [?s [?s [?H [?H _]]]]
  | _ ;;; _ |-w _ : wHeq _ _ _ _ _ =>
    let XX := fresh "H" in
    gitt_as H XX;
    eapply inversion_Heq in XX;
    destruct XX as [?H [?H [?H [?H _]]]]
  end.

Definition wHeqPi1 s A a B b p :=
  wPi1 (wEq (wSort s) A B) (wEq (↑ B) (wcoe s (↑ A) (↑ B) (wRel 0) (↑ a)) (↑ b)) p.

Definition type_HeqPi1 Γ A a B b p s :
    Σ ;;; Γ |-w p : wHeq s A a B b ->
    Σ ;;; Γ |-w wHeqPi1 s A a B b p : wEq (wSort s) A B.
Proof.
  intros H. unfold wHeqPi1, wHeq in *. ittcheck.
Defined.

Definition lift_HeqPi1 A a B b p s n k :
  lift n k (wHeqPi1 s A a B b p)
  = wHeqPi1 s (lift n k A) (lift n k a) (lift n k B) (lift n k b) (lift n k p).
Proof.
  cbn.
  rewrite !(liftP2 _ 0 1) by omega. reflexivity.
Defined.

Definition subst_HeqPi1 A a B b p s n t :
  (wHeqPi1 s A a B b p){n := t}
  = wHeqPi1 s (A{n := t}) (a{n := t}) (B{n := t}) (b{n := t}) (p{n := t}).
Proof.
  cbn. rewrite !(substP2 _ _ 0 1) by omega. reflexivity.
Defined.

Definition wHeqPi2 s A a B b p :=
  wPi2 (wEq (wSort s) A B) (wEq (↑ B) (wcoe s (↑ A) (↑ B) (wRel 0) (↑ a)) (↑ b)) p.

Definition type_HeqPi2 Γ A a B b p s :
    Σ ;;; Γ |-w p : wHeq s A a B b ->
    Σ ;;; Γ |-w wHeqPi2 s A a B b p : wEq B (wcoe s A B (wHeqPi1 s A a B b p) a) b.
Proof.
  intros H. unfold wHeqPi1, wHeqPi2, wHeq in *. ittcheck.
  Unshelve.
  cbn; substP3.
Defined.

Definition wHeqPair s A a B b p q :=
  wPair (wEq (wSort s) A B) (wEq (↑ B) (wcoe s (↑ A) (↑ B) (wRel 0) (↑ a)) (↑ b))
        p q.

Definition type_HeqPair Γ A a B b p q s :
    wf Σ Γ ->
    Σ ;;; Γ |-w p : wEq (wSort s) A B ->
    Σ ;;; Γ |-w q : wEq B (wcoe s A B p a ) b ->
    Σ ;;; Γ |-w wHeqPair s A a B b p q : wHeq s A a B b.
Proof.
  intros HΓ H H0.
  inverse H. inverse H0.
  unfold wHeqPair, wHeq in *. ittcheck.
  eapply inversionJ in H5.
  destruct H5 as [?s1 [?s2 [?H3 [H3' [H3'' [H33 [H34 [H35 eq3]]]]]]]].
  clear - H35. cbn in H35; now rewrite substP3, lift00 in H35 by omega.
  Unshelve. cbn; substP3.
Qed.

Opaque wHeq wcoe wtransport wHeqPi1 wHeqPi2 wHeqPair.
Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
  | wHeqPi1 _ _ _ _ _ _ => eapply type_HeqPi1
  | wHeqPi2 _ _ _ _ _ _ => eapply type_HeqPi2
  | wHeqPair _ _ _ _ _ _ _ => eapply type_HeqPair
  | _ => fail "No introduction rule for" t
  end.



Notation "'pack_sort' s" :=
  (sum_sort s (sum_sort s (sum_sort (eq_sort (succ s)) (eq_sort s)))) (at level 30).

Definition wPack s A1 A2 :=
  wSum (nNamed "x1") A1 (wSum (nNamed "x2") (↑ A2)
                              (wHeq s (↑ (↑ A1)) (wRel 1) (↑ (↑ A2)) (wRel 0))).
Definition type_Pack Γ s A1 A2 :
    wf Σ Γ ->
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w wPack s A1 A2 : wSort (pack_sort s).
Proof.
  intros HΓ HA1 HA2; unfold wPack.
  ittcheck.
Defined.

Definition lift_Pack s A1 A2 n k :
  lift n k (wPack s A1 A2) = wPack s (lift n k A1) (lift n k A2).
Proof.
  unfold wPack; cbn.
  rewrite lift_heq; cbn.
  now rewrite !(liftP2 _ 0 1) by omega.
Qed.


Definition wpack s A1 A2 u1 u2 p :=
  wPair A1 (wSum (nNamed "x2") (↑ A2) (wHeq s (↑ (↑ A1)) (wRel 1) (↑ (↑ A2)) (wRel 0))) u1 (wPair A2 (wHeq s (↑ A1) (↑ u1) (↑ A2) (wRel 0)) u2 p).

Definition type_pack Γ s A1 A2 u1 u2 p :
    wf Σ Γ ->
    Σ ;;; Γ |-w u1 : A1 ->
    Σ ;;; Γ |-w u2 : A2 ->
    Σ ;;; Γ |-w p : wHeq s A1 u1 A2 u2 ->
    Σ ;;; Γ |-w wpack s A1 A2 u1 u2 p : wPack s A1 A2.
(* Proof with try assumption. *)
(*   intros H H0 H1 H2.  eexists. inverse H2. *)
(*   eapply type_Pair... eassumption. *)
(*   ittcheck. cbn. rewrite !lift_lift, subst_heq. substP3; cbn. *)
(*   eapply type_Pair... eassumption. ittcheck. *)
(*   rewrite subst_heq. substP3; cbn. rewrite lift00. eassumption. *)
(* Defined. *)
Proof.
  intros H H0 H1 H2; unfold wpack. inverse H2. ittcheck.
  Unshelve. shelve.
  all: cbn; rewrite subst_heq, ?lift_lift; cbn; substP3.
Qed.


Definition wProjT1 s A1 A2 p :=
  wPi1 A1 (wSum (nNamed "x2") (↑ A2)
                (wHeq s (↑ (↑ A1)) (wRel 1) (↑ (↑ A2)) (wRel 0))) p.

Definition type_ProjT1 Γ s A1 A2 p :
    Σ ;;; Γ |-w p : wPack s A1 A2 ->
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w wProjT1 s A1 A2 p : A1.
Proof.
  intros H H0 H1; unfold wProjT1; ittcheck. 
Defined.

Definition wProjT2 s A1 A2 p :=
  wPi1 A2 (wHeq s (↑ A1) (↑ (wProjT1 s A1 A2 p)) (↑ A2) (wRel 0))
       (wPi2 A1 (wSum (nNamed "x2") (↑ A2)
                (wHeq s (↑ (↑ A1)) (wRel 1) (↑ (↑ A2)) (wRel 0))) p).

Definition subst_ProjT1 s A1 A2 p n t
  : (wProjT1 s A1 A2 p) {n := t}
    = wProjT1 s (A1 { n := t}) (A2 { n := t}) (p { n := t}).
Proof.
  cbn; eapply (f_equal (fun X => wPi1 _ X _)).
  rewrite (substP2 _ _ 0 1 n) by omega. eapply f_equal.
  rewrite subst_heq; cbn.
  rewrite !(substP2 _ _ 0 1 (Datatypes.S n)) by omega.
  now rewrite !(substP2 _ _ 0 1 n) by omega.
Qed.


Definition type_ProjT2 Γ s A1 A2 p :
    Σ ;;; Γ |-w p : wPack s A1 A2 ->
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w wProjT2 s A1 A2 p : A2.
Proof.
  intros H H0 H1; unfold wProjT2; ittcheck. 
  Unshelve. shelve.
  cbn; substP3.
  rewrite subst_heq. cbn.
  rewrite !lift_lift.
  substP3.
Defined.

Definition subst_ProjT2 s A1 A2 p n t
  : (wProjT2 s A1 A2 p) {n := t}
    = wProjT2 s (A1 { n := t}) (A2 { n := t}) (p { n := t}).
Proof. unfold wProjT2.
  cbn.
  rewrite !(substP2 _ _ 0 1 n) by omega.
  rewrite !subst_heq; cbn.
  rewrite !lift_heq; cbn.
  rewrite !(substP2 _ _ 0 1 (Datatypes.S n)) by omega.
  rewrite !(substP2 _ _ 0 1 n) by omega.
  rewrite !(substP2 _ _ 1 1 (Datatypes.S n)) by omega.
Admitted.

Definition wProjTe s A1 A2 p :=
  wPi2 A2 (wHeq s (↑ A1) (↑ (wProjT1 s A1 A2 p)) (↑ A2) (wRel 0))
       (wPi2 A1 (wSum (nNamed "x2") (↑ A2)
                (wHeq s (↑ (↑ A1)) (wRel 1) (↑ (↑ A2)) (wRel 0))) p).

Definition type_ProjTe Γ s A1 A2 p :
    Σ ;;; Γ |-w p : wPack s A1 A2 ->
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w wProjTe s A1 A2 p : wHeq s A1 (wProjT1 s A1 A2 p)
                                          A2 (wProjT2 s A1 A2 p).
Proof.
  intros H H0 H1; unfold wProjTe; ittcheck. 
  Unshelve. shelve.
  - cbn. substP3.
    rewrite subst_heq. cbn.
    rewrite !lift_lift. substP3.
  - rewrite subst_heq. substP3. apply f_equal.
    cbn. rewrite !lift00; reflexivity.
Defined.

Opaque wPack wpack wProjT1 wProjT2 wProjTe.
Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
  | wHeqPi1 _ _ _ _ _ _ => eapply type_HeqPi1
  | wHeqPi2 _ _ _ _ _ _ => eapply type_HeqPi2
  | wHeqPair _ _ _ _ _ _ _ => eapply type_HeqPair
  | wPack _ _ _ => eapply type_Pack
  | wpack _ _ _ _ _ _ => eapply type_pack
  | wProjT1 _ _ _ _ => eapply type_ProjT1
  | wProjT2 _ _ _ _ => eapply type_ProjT2
  | wProjTe _ _ _ _ => eapply type_ProjTe
  | _ => fail "No introduction rule for" t
  end.


Definition wconcat A x y z p q
  := wtransport A (wEq (↑ A) (↑ x) (wRel 0)) y z q p.

Definition type_concat Γ A x y z p q :
      wf Σ Γ ->
      Σ ;;; Γ |-w p : wEq A x y ->
      Σ ;;; Γ |-w q : wEq A y z ->
      Σ ;;; Γ |-w wconcat A x y z p q : wEq A x z.
Proof.
  intros HΓ Hp Hq; unfold wconcat.
  inverse Hp. ittcheck.
  Unshelve. all: cbn; substP3.
Defined.


Definition winverse A x y p
  := wtransport A (wEq (↑ A) (wRel 0) (↑ x)) x y p (wRefl A x).

Definition type_inverse Γ A x y p :
      wf Σ Γ ->
      Σ ;;; Γ |-w p : wEq A x y ->
      Σ ;;; Γ |-w winverse A x y p : wEq A y x.
Proof.
  intros HΓ Hp; unfold winverse.
  inverse Hp. ittcheck.
  Unshelve. all: cbn; substP3.
Defined.

Definition wap A B f x y p :=
  wtransport A (wEq ⇑B (wApp ⇑f ⇑x) (wApp ⇑f (wRel 0))) x y p (wRefl B (wApp f x)).

Definition type_ap Γ A B f x y p :
      wf Σ Γ ->
      Σ ;;; Γ |-w f : A ↦ B ->
      Σ ;;; Γ |-w p : wEq A x y ->
      Σ ;;; Γ |-w wap A B f x y p : wEq B (wApp f x) (wApp f y).
(* Proof with try assumption. *)
(*   intros HΓ Hf Hp; unfold winverse. eexists. *)
(*   inverse Hp. inverse Hf. *)
(*   eapply meta_conv. *)
(*   eapply type_transport with (P:=wEq ⇑B (wApp ⇑f ⇑x) (wApp ⇑f (wRel 0)))... *)
(*   2: eassumption. *)
(*   ittcheck. *)
(*   all: cbn; substP3. eapply type_Refl; ittcheck. *)
(*   Unshelve. *)
(*   all: rewrite ?liftP3 by omega; substP3. *)
(* Defined. *)
Proof.
  intros H H0 H1; unfold wap. inverse H0. inverse H1.
  ittcheck.
  Unshelve.
  all: cbn; rewrite ?liftP3 by omega; substP3.
Qed.


Definition wcoeβ A t :=
  wJBeta A (wRel 1) t.

Definition  type_coeβ Γ s A t :
    wf Σ Γ ->
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w wcoeβ A t
             : wEq A (wcoe s A A (wRefl (wSort s) A) t) t.
Proof.
  intros H H0 H1; unfold wcoeβ. ittcheck.
  Unshelve. all: cbn; substP3.
Defined.

Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
  | wHeqPi1 _ _ _ _ _ _ => eapply type_HeqPi1
  | wHeqPi2 _ _ _ _ _ _ => eapply type_HeqPi2
  | wHeqPair _ _ _ _ _ _ _ => eapply type_HeqPair
  | wPack _ _ _ => eapply type_Pack
  | wpack _ _ _ _ _ _ => eapply type_pack
  | wProjT1 _ _ _ _ => eapply type_ProjT1
  | wProjT2 _ _ _ _ => eapply type_ProjT2
  | wProjTe _ _ _ _ => eapply type_ProjTe
  | winverse _ _ _ _ => eapply type_inverse
  | wconcat _ _ _ _ _ _ => eapply type_concat
  | wap _ _ _ _ _ _ => eapply type_ap
  | wcoeβ _ _ => eapply type_coeβ
  | _ => fail "No introduction rule for" t
  end.

Definition wcoeβ' s A e t :=
  wconcat A (wcoe s A A e t) (wcoe s A A (wRefl (wSort s) A) t) t (wtransport (wEq (wSort s) A A) (wEq (↑ A) (wcoe s (↑ A) (↑ A) (↑ e) (↑ t)) (wcoe s (↑ A) (↑ A) (wRel 0) (↑ t))) e (wRefl (wSort s) A) (wK (wSort s) A e) (wRefl A (wcoe s A A e t))) (wcoeβ A t).

Definition  type_coeβ' Γ s A e t :
    wf Σ Γ ->
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w e : wEq (wSort s) A A ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w wcoeβ' s A e t : wEq A (wcoe s A A e t) t.
Proof.
  intros H H0 H1 H2. unfold wcoeβ'. ittcheck.
  Unshelve.
  cbn. rewrite !subst_coe. cbn. substP3.
  cbn. rewrite !subst_coe. cbn. substP3.
Defined.

Opaque winverse wconcat wap wcoeβ wcoeβ'.
Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
  | wHeqPi1 _ _ _ _ _ _ => eapply type_HeqPi1
  | wHeqPi2 _ _ _ _ _ _ => eapply type_HeqPi2
  | wHeqPair _ _ _ _ _ _ _ => eapply type_HeqPair
  | wPack _ _ _ => eapply type_Pack
  | wpack _ _ _ _ _ _ => eapply type_pack
  | wProjT1 _ _ _ _ => eapply type_ProjT1
  | wProjT2 _ _ _ _ => eapply type_ProjT2
  | wProjTe _ _ _ _ => eapply type_ProjTe
  | winverse _ _ _ _ => eapply type_inverse
  | wconcat _ _ _ _ _ _ => eapply type_concat
  | wap _ _ _ _ _ _ => eapply type_ap
  | wcoeβ _ _ => eapply type_coeβ
  | wcoeβ' _ _ _ _ => eapply type_coeβ'
  | _ => fail "No introduction rule for" t
  end.



(* Definition type_HeqToEq Γ A u v p s : *)
(*     wf Σ Γ -> *)
(*     Σ ;;; Γ |-w p : wHeq s A u A v -> *)
(* exists wHeqToEq, *)
(*     Σ ;;; Γ |-w wHeqToEq : wEq A u v. *)
(* Proof. *)
(*   intros H H0. eexists. inverse H0. *)
(*   eapply type_concat. assumption. *)
(*   2: eapply type_HeqPi2; eassumption. *)
(*   eapply type_inverse. assumption. *)
(*   eapply type_coeβ'; ittcheck. *)
(* Qed. *)

Definition wHeqToEq A u v p s :=
  wconcat A u (wcoe s A A (wHeqPi1 s A u A v p) u) v
          (winverse A (wcoe s A A (wHeqPi1 s A u A v p) u) u
                    (wcoeβ' s A (wHeqPi1 s A u A v p) u)) (wHeqPi2 s A u A v p).

Definition type_HeqToEq Γ A u v p s :
    wf Σ Γ ->
    Σ ;;; Γ |-w p : wHeq s A u A v ->
    Σ ;;; Γ |-w wHeqToEq A u v p s : wEq A u v.
Proof.
  intros H H0. inverse H0.
  unfold wHeqToEq; ittcheck.
Qed.


Definition wEqToHeq s A u v p :=
  wHeqPair s A u A v (wRefl (wSort s) A)
           (wconcat A (wcoe s A A (wRefl (wSort s) A) u) u v (wcoeβ A u) p).

Definition type_EqToHeq Γ A u v p s :
    wf Σ Γ ->
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w p : wEq A u v ->
    Σ ;;; Γ |-w wEqToHeq s A u v p : wHeq s A u A v.
Proof.
  intros H H0 H1; unfold wEqToHeq. inverse H1. ittcheck.
Qed.
(* Proof with try assumption. *)
(*   intros H H0 H1. eexists. inverse H1. *)
(*   eapply type_HeqPair... eapply type_Refl... *)
(*   eapply type_concat... eapply type_coeβ... *)
(*   eassumption. *)
(* Qed. *)


Definition wHeqRefl s A a := wEqToHeq s A a a (wRefl A a).

Definition type_HeqRefl Γ A a s :
    wf Σ Γ ->
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w a : A ->
    Σ ;;; Γ |-w wHeqRefl s A a : wHeq s A a A a.
Proof.
  intros H H0 H1; unfold wHeqRefl; eapply type_EqToHeq; ittcheck.
Qed.


Definition type_HeqSym0 Γ A a B b p s :
    wf Σ Γ ->
    Σ ;;; Γ |-w p : wHeq s A a B b ->
                   exists wHeqSym,
    Σ ;;; Γ |-w wHeqSym : wHeq s B b A a.
Proof with try assumption.
  intros. eexists.
  inverse H0.
  refine ( let XX : Σ ;;; Γ |-w _ : wProd nAnon B (wProd nAnon (wEq ⇑B (wcoe s ⇑A ⇑B ⇑(wHeqPi1 s A a B b p) ⇑a) (wRel 0)) (wHeq s (lift 2 0 B) (wRel 1) (lift 2 0 A) (lift 2 0 a))) := _ in _).
  eapply meta_conv. eapply type_App.
  2: eapply type_HeqPi2; eassumption.
  eapply meta_conv. eapply type_App.
  exact XX. eassumption.
  Opaque wHeq.
  cbn; rewrite subst_heq, subst_coe; cbn; substP3.
  rewrite subst_heq; cbn; substP3.
  
  Unshelve. 2: shelve.
  rewrite lift_HeqPi1; cbn. eapply meta_conv.
  eapply type_J...
  2: eapply type_HeqPi1; eassumption.
  Unshelve.
  4: exact (wProd nAnon (wRel 1) (wProd nAnon (wEq (wRel 2) (wcoe s (lift0 3 A) (wRel 2) (wRel 1) (lift0 3 a)) (wRel 0)) (wHeq s (wRel 3) (wRel 1) (lift0 4 A) (lift0 4 a)))).
  3: cbn; rewrite !subst_heq, !subst_coe; cbn; substP3; now rewrite lift_HeqPi1.
  - ittcheck.
  - cbn; rewrite !subst_heq, !subst_coe; cbn; substP3; cbn.
    eapply type_Lambda. eapply type_Lambda. ittcheck.
    eapply type_HeqPair. ittcheck.
    + ittcheck. eapply type_Refl... ittcheck.
    + eapply type_concat. ittcheck.
      eapply type_coeβ; ittcheck.
      eapply type_concat. ittcheck.
      eapply type_inverse. ittcheck.
      * eapply meta_conv. eapply type_Rel with (n := 0). ittcheck.
        cbn. rewrite lift_coe. now rewrite !liftP3 by omega; cbn.
      * rewrite !liftP3 by omega; cbn. eapply type_coeβ; ittcheck.

    Unshelve.
    all: try exact nAnon.
    all: cbn; try omega.
    all: now rewrite liftP3 by omega.
Defined.

Definition wHeqSym A a B b p s :=
wApp (wApp (wJ (wSort s) A (wProd nAnon (wRel 1) (wProd nAnon (wEq (wRel 2) (wcoe s (lift0 3 A) (wRel 2) (wRel 1) (lift0 3 a)) (wRel 0)) (wHeq s (wRel 3) (wRel 1) (lift0 4 A) (lift0 4 a)))) (wLambda nAnon A (wLambda nAnon (wEq ⇑A (wcoe s ⇑A ⇑A (wRefl (wSort s) ⇑A) ⇑a) (wRel 0)) (wHeqPair s (lift0 2 A) (wRel 1) (lift0 2 A) (lift0 2 a) (wRefl (wSort s) (lift0 2 A)) (wconcat (lift0 2 A) (wcoe s (lift0 2 A) (lift0 2 A) (wRefl (wSort s) (lift0 2 A)) (wRel 1)) (wRel 1) (lift0 2 a) (wcoeβ (lift0 2 A) (wRel 1)) (wconcat (lift0 2 A) (wRel 1) (wcoe s (lift0 2 A) (lift0 2 A) (wRefl (wSort s) (lift0 2 A)) (lift0 2 a)) (lift0 2 a) (winverse (lift0 2 A) (wcoe s (lift0 2 A) (lift0 2 A) (wRefl (wSort s) (lift0 2 A)) (lift0 2 a)) (wRel 1) (wRel 0)) (wcoeβ (lift0 2 A) (lift0 2 a))))))) B (wHeqPi1 s A a B b p)) b) (wHeqPi2 s A a B b p).

Definition type_HeqSym Γ A a B b p s :
    wf Σ Γ ->
    Σ ;;; Γ |-w p : wHeq s A a B b ->
    Σ ;;; Γ |-w wHeqSym A a B b p s : wHeq s B b A a.
Proof.
  intros H H0; unfold wHeqSym. inverse H0. clear s0.
  ittcheck.
  Unshelve.

  all: try exact nAnon.
  all: simpl; rewrite ?lift_coe, ?lift_P3 by omega; simpl;
    rewrite ?lift_lift by omega; try reflexivity; simpl.
  rewrite !subst_coe, !subst_heq; cbn; substP3.
  change (B = ⇑B {0 := wHeqPi1 s A a B b p}). substP3.
  change (wEq B (wcoe s A B (wHeqPi1 s A a B b p) a) b = wEq (((lift0 2 B) {1 := wHeqPi1 s A a B b p}) {0 := b}) ((wcoe s (lift0 3 A) (wRel 2) (wRel 1) (lift0 3 a)) {2 := B} {1 := wHeqPi1 s A a B b p} {0 := b}) (lift0 0 b)).
  rewrite !subst_coe. substP3.
  change ((wHeq s (wRel 3) (wRel 1) (lift0 4 A) (lift0 4 a)){3:= B}{2 := wHeqPi1 s A a B b p}{1 := b}{0 := wHeqPi2 s A a B b p} = wHeq s B b A a).
  rewrite !subst_heq. substP3.
Qed.

Axiom wHeqTrans : forall (A a B b C c p q : wterm)(s : sort), wterm.

Definition type_HeqTrans Γ A a B b C c p q s :
    wf Σ Γ ->
    Σ ;;; Γ |-w p : wHeq s A a B b ->
    Σ ;;; Γ |-w q : wHeq s B b C c ->
    Σ ;;; Γ |-w wHeqTrans A a B b C c p q s : wHeq s A a C c.
Proof.
Admitted.



Opaque wHeqToEq wEqToHeq wHeqRefl wHeqSym wHeqTrans.
Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
  | wHeqPi1 _ _ _ _ _ _ => eapply type_HeqPi1
  | wHeqPi2 _ _ _ _ _ _ => eapply type_HeqPi2
  | wHeqPair _ _ _ _ _ _ _ => eapply type_HeqPair
  | wPack _ _ _ => eapply type_Pack
  | wpack _ _ _ _ _ _ => eapply type_pack
  | wProjT1 _ _ _ _ => eapply type_ProjT1
  | wProjT2 _ _ _ _ => eapply type_ProjT2
  | wProjTe _ _ _ _ => eapply type_ProjTe
  | winverse _ _ _ _ => eapply type_inverse
  | wconcat _ _ _ _ _ _ => eapply type_concat
  | wap _ _ _ _ _ _ => eapply type_ap
  | wcoeβ _ _ => eapply type_coeβ
  | wcoeβ' _ _ _ _ => eapply type_coeβ'
  | wHeqToEq _ _ _ _ _  => eapply type_HeqToEq
  | wEqToHeq _ _ _ _ _  => eapply type_EqToHeq
  | wHeqRefl _ _ _  => eapply type_HeqRefl
  | wHeqSym _ _ _ _ _ _  => eapply type_HeqSym
  | wHeqSym _ _ _ _ _ _ _ _ _  => eapply type_HeqTrans
  | _ => fail "No introduction rule for" t
  end.


End Manual.

(* Definition type_smld Γ s z k A1 A2 B1 B2 pA pB P P1 : *)
(*     wf Σ Γ -> *)
(*     Σ ;;; Γ ,, A1 |-w B1 : wSort z -> *)
(*     Σ ;;; Γ ,, A2 |-w B2 : wSort z -> *)
(*     Σ ;;; Γ |-w pA : wHeq (succ s) (wSort s) A1 (wSort s) A2 -> *)
(*     Σ ;;; Γ ,, (wPack s A1 A2) *)
(*     |-w pB : wHeq (succ z) *)
(*                  (wSort z) ((lift 1 1 B1){ 0 := wProjT1 s ⇑A1 ⇑A2 (wRel 0) }) *)
(*                  (wSort z) ((lift 1 1 B2){ 0 := wProjT2 s ⇑A1 ⇑A2 (wRel 0) }) -> *)
(*     Σ ;;; Γ ,, wSort s ,, (wRel 0 ↦ wSort z) |-w P : wSort k -> *)
(*     Σ ;;; Γ |-w P1 : P { 1 := A1 } { 0 := wLambda nAnon A1 B1 } -> *)
(* exists P2, *)
(*     Σ ;;; Γ |-w P2 : P { 1 := A2 } { 0 := wLambda nAnon A2 B2 }. *)
(* Proof with try assumption. *)
(*   intros HΓ HB1 HB2 HA12 HB12 HP HP1. *)
(*   eexists. inverse HA12. clear s0 HA0 HA2. rename HA3 into HA2. *)
(*   (* assert (isType Σ Γ ((P {1 := A2}) {0 := wLambda nAnon A2 B2})). { *) *)
(*   (*   eexists. eapply meta_conv. eapply typing_subst2; try eassumption. *) *)
(*   (*   2: reflexivity. cbn. rewrite lift00. *) *)
(*   (*   ittcheck. } *) *)
(*   refine (let XX : Σ ;;; Γ |-w _ : wProd nAnon (A2 ↦ wSort z) *)
(*           ((wProd nAnon ⇑(wPack s A1 A2) (wHeq (succ z) (wSort z) *)
(*           ((lift 2 1 B1) {0 := wProjT1 s (lift0 2 A1) (lift0 2 A2) (wRel 0)})  *)
(*           (wSort z) (wApp (wRel 1) (wProjT2 s (lift0 2 A1) (lift0 2 A2) (wRel 0))))) *)
(*              ↦ (⇑((P {1 := A2}) {0 := wLambda nAnon A2 B2}))) *)
(*               := _ in _). *)
(*   - eapply meta_conv. eapply type_App. *)
(*     eapply meta_conv. eapply type_App. exact XX. *)
(*     all: clear XX. *)
(*     + eapply type_Lambda; eassumption. *)
(*     + cbn; rewrite !subst_heq; cbn; substP3.  *)
(*     + eapply type_Lambda. eapply type_HeqTrans. ittcheck. *)
(*       eapply meta_conv. exact HB12. *)
(*       * apply (f_equal (fun X => wHeq _ _ X _ _)). *)
(*       rewrite (substP4 _ _ _ 0 1); cbn. *)
(*       rewrite (substP3 _ _ 1 2 1) by omega. *)
(*       rewrite subst_ProjT1; cbn. *)
(*       now rewrite !(substP3 _ _ 0) by omega. *)
(*       * eapply type_EqToHeq; ittcheck. *)
(*         rewrite subst_ProjT2; cbn. *)
(*         rewrite !(substP3 _ _ 0 1 1) by omega. *)
(*         eapply meta_conv. eapply type_inverse. ittcheck. *)
(*         eapply type_Beta with (A := ⇑A2) (t := lift 1 1 B2) *)
(*                               (u := wProjT2 s ⇑A1 ⇑A2 (wRel 0)); ittcheck. *)
(*       eapply (@type_lift S Σ Γ [_] [_]); ittcheck. reflexivity. *)
(*     + rewrite lift_lift; cbn. *)
(*       rewrite !(substP3 _ _ 0) by omega. *)
(*       now rewrite lift00. *)

(*       Unshelve. all: try exact nAnon. 2: shelve. 2: apply lift_Pack. *)
(*       eapply meta_conv. *)
(*       eapply type_HeqToEq in HA12; try assumption. *)
(*       eapply type_transport with (P := lift 1 1 (wProd nAnon (wRel 0 ↦ wSort z) (wProd nAnon ⇑(wPack s A1 (wRel 0)) (wHeq (succ z) (wSort z) ((lift 2 1 B1) {0 := wProjT1 s (lift0 2 A1) (lift0 2 (wRel 0)) (wRel 0)}) (wSort z) (wApp (wRel 1) (wProjT2 s (lift0 2 A1) (lift0 2 (wRel 0)) (wRel 0)))) ↦ ⇑((P {1 := (wRel 0)}) {0 := wLambda nAnon (wRel 0) B2})))). *)
(*       assumption. 2: exact HA12. *)
(*       * cbn. rewrite !lift_Pack, !lift_heq, !lift_lift; cbn. *)
(*         admit. *)
(*       * cbn. rewrite !lift_Pack, !lift_heq, !lift_lift, !lift00; cbn. *)
(*         repeat eapply type_Lambda. *)
(*       * *)
(*  ittcheck. *)
(*         rewrite !lift_Pack. ittcheck; cbn. admit. *)
(*         ittcheck. admit. *)
(*       eapply (@type_lift S Σ _ [_] [_; _]); ittcheck. reflexivity. *)
(*   . *)

(*       eapply type_Lambda. eapply type_Lambda.  *)

(*   cbn. eapply type_heq. *)
(*   ittcheck. *)
(*   eapply type_App. *)

(*    (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) -> *)
(*   P A2 B2 *)

(* Admitted. *)

(* Definition wsmld (s z k : sort) (A1 A2 B1 B2 pA pB P P1 : wterm) : wterm. *)
(* Admitted. *)

(* Definition type_smld Γ s z k A1 A2 B1 B2 pA pB P P1 : *)
(*     wf Σ Γ -> *)
(*     Σ ;;; Γ ,, A1 |-w B1 : wSort z -> *)
(*     Σ ;;; Γ ,, A2 |-w B2 : wSort z -> *)
(*     Σ ;;; Γ |-w pA : wHeq (succ s) (wSort s) A1 (wSort s) A2 -> *)
(*     Σ ;;; Γ ,, (wPack s A1 A2) *)
(*     |-w pB : wHeq (succ z) *)
(*                  (wSort z) ((lift 1 1 B1){ 0 := wProjT1 s ⇑A1 ⇑A2 (wRel 0) }) *)
(*                  (wSort z) ((lift 1 1 B2){ 0 := wProjT2 s ⇑A1 ⇑A2 (wRel 0) }) -> *)
(*     Σ ;;; Γ ,, wSort s ,, (wRel 0 ↦ wSort z) |-w P : wSort k -> *)
(*     Σ ;;; Γ |-w P1 : P { 1 := A1 } { 0 := wLambda nAnon A1 B1 } -> *)
(*     Σ ;;; Γ |-w wsmld s z k A1 A2 B1 B2 pA pB P P1 *)
(*              : P { 1 := A2 } { 0 := wLambda nAnon A2 B2 }. *)
(* Admitted. *)


(* Lemma subst_rel0 t : forall k, (lift 1 (1 + k)%nat t) {k := wRel 0} = t. *)
(*   induction t; intro k; cbn. *)
(*   { destruct n. cbn. case_eq k; reflexivity. *)
(*     nat_case; cbn; nat_case; cbn; try reflexivity. *)
(*     now rewrite e2, Nat.add_0_r. } *)
(*   all: repeat hyp rewrite; try reflexivity. *)
(* Defined. *)


(* Definition type_CongProd Γ s z nx ny A1 A2 B1 B2 pA pB : *)
(*     wf Σ Γ -> *)
(*     Σ ;;; Γ ,, A1 |-w B1 : wSort z -> *)
(*     Σ ;;; Γ ,, A2 |-w B2 : wSort z -> *)
(*     Σ ;;; Γ |-w pA : wHeq (succ s) (wSort s) A1 (wSort s) A2 -> *)
(*     Σ ;;; Γ ,, (wPack s A1 A2) *)
(*     |-w pB : wHeq (succ z) *)
(*                  (wSort z) ((lift 1 1 B1){ 0 := wProjT1 s ⇑A1 ⇑A2 (wRel 0) }) *)
(*                  (wSort z) ((lift 1 1 B2){ 0 := wProjT2 s ⇑A1 ⇑A2 (wRel 0) }) -> *)
(* exists XX, *)
(*     Σ ;;; Γ |-w XX : *)
(*     wHeq (succ (Sorts.prod_sort s z)) *)
(*          (wSort (Sorts.prod_sort s z)) (wProd nx A1 B1) *)
(*          (wSort (Sorts.prod_sort s z)) (wProd ny A2 B2). *)
(* Proof. *)
(*   intros HΓ HB1 HB2 HA12 HB12.  *)
(*   eexists. inverse HA12. clear s0 HA0 HA2. rename HA3 into HA2. *)
(*   unshelve eapply type_HeqTrans. exact (wSort (Sorts.prod_sort s z)). *)
(*   exact (wProd ny A2 (wApp (wLambda nAnon ⇑A2 (lift 1 1 B2)) (wRel 0))). *)
(*   shelve. shelve. assumption. *)

(*   - eapply meta_conv. *)
(*     pose (P := wHeq (succ (Sorts.prod_sort s z)) *)
(*         (wSort (Sorts.prod_sort s z)) (lift0 2 (wProd nx A1 B1)) *)
(*         (wSort (Sorts.prod_sort s z)) (wProd ny (wRel 1) (wApp (wRel 1) (wRel 0)))). *)
(*     refine (type_smld _ _ _ _ _ _ _ _ _ _ P _ HΓ HB1 HB2 HA12 HB12 _ _); subst P. *)
(*     + ittcheck. *)
(*     + rewrite !subst_heq; cbn. substP3. *)
(*       simple refine (let XX := type_Beta Σ HΣ (Γ ,, A1) ⇑A1 (wSort z) (lift 1 1 B1) *)
(*                                          (wRel 0) _ _ _ in _). *)
(*       constructor. *)
(*       eapply meta_conv. *)
(*       eapply (@type_lift S Σ Γ [_] [_]); ittcheck. reflexivity. *)
(*       ittcheck. rewrite subst_rel0 in XX; cbn in XX. *)
(*       eapply type_EqToHeq. assumption. ittcheck. *)
(*       eapply type_ProdExt. eapply type_inverse; ittcheck. assumption. *)
(*     + rewrite !subst_heq; cbn. substP3. *)
(*   - eapply type_EqToHeq. assumption. ittcheck. *)
(*     eapply type_ProdExt. *)
(*     simple refine (let XX := type_Beta Σ HΣ (Γ ,, A2) ⇑A2 (wSort z) (lift 1 1 B2) *)
(*                                        (wRel 0) _ _ _ in _). *)
(*     constructor. eapply meta_conv. *)
(*     eapply (@type_lift S Σ Γ [_] [_]); ittcheck. reflexivity. *)
(*     ittcheck. rewrite subst_rel0 in XX; cbn in XX. *)
(*     all: eassumption. *)
(* Defined. *)


(* Γ , A ⊢ B1 : wSort s *)
(* Γ , A ⊢ B2 : wSort s *)
(* Γ , A ⊢ pB : wEq (wSort s) B1 B2 *)

(* Γ ⊢ ? : wEq (wSort ...) (wProd A B1) (wProd A B2) *)

(*   cbn in H3. rewrite subst_rel0 in H3. *)
(*   pose proof (substP3 B1 (wRel 0) 0 0 1).  cbn in H4. in H3. by omega. *)
(*   change () *)




(* Lemma heq_to_eq_fam'@{i i1 i2 j j1 j2 ij1 k i1j2k} {A1 A2 : Type@{i}} *)
(*       {B1 : A1 -> Type@{j}} {B2 : A2 -> Type@{j}} *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p))) *)
(*       (P : forall (A : Type@{i})(B : A -> Type@{j}), Type@{k}) *)
(*       (P1 : P A1 B1) *)
(*   : P A2 B2. *)
(* Proof. *)
(*   revert B2 hB. refine (transport@{i1 i1j2k} (fun A2: Type@{i} => forall B2 : A2 -> Type@{j}, (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) -> P A2 B2) (heq_to_eq hA) _). *)
(*   intros B2 hB. refine (transport@{ij1 k} _ _ P1). apply funext; intro x. *)
(*   refine (_ @ heq_to_eq (hB (pack x x (heq_refl x))) @ _). *)
(*   all: apply ap. symmetry; apply ProjT1β. apply ProjT2β. *)
(* Defined. *)



  
(*   let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.ProjT1β" in *)
(*   let TC := tsl_constant TC [pvar 0; pvar 1; psum_sort (pvar 0) (pvar 1)] "Translation.Quotes.transport_sigma_const" in *)
(*   let TC := tsl_constant TC [pvar 0; psucc (pvar 0)] "Translation.Quotes.ProjT2β" in *)
(*   let TC := tsl_constant TC [pvar 0; psucc (pvar 0); pvar 1; psucc (pvar 1); psucc (psucc (pvar 1)); psucc (pprod_sort (pvar 0) (pvar 1))] "Translation.Quotes.heq_to_eq_fam" in *)



(* | type_HeqTrans Γ A a B b C c p q s : *)
(*     Σ ;;; Γ |-i p : sHeq A a B b -> *)
(*     Σ ;;; Γ |-i q : sHeq B b C c -> *)
(*     Σ ;;; Γ |-i a : A -> *)
(*     Σ ;;; Γ |-i b : B -> *)
(*     Σ ;;; Γ |-i c : C -> *)
(*     Σ ;;; Γ |-i A : sSort s -> *)
(*     Σ ;;; Γ |-i B : sSort s -> *)
(*     Σ ;;; Γ |-i C : sSort s -> *)
(*     Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c *)
