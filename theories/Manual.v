(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template
Require Import Ast utils monad_utils Typing Checker.
From Translation
Require Import util Sorts WAst WLiftSubst WTyping WChecker WLemmata Quotes.
From TypingFlags Require Import Loader.
Import MonadNotation ListNotations.

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
    let X1 := fresh "H" in
    let X2 := fresh "H" in
    let X3 := fresh "H" in
    let s := fresh "s" in
    destruct XX as [s [X1 [X2 [X3 _]]]]
  end.


Section Admissibles1.
  Context {S : notion} Σ (HΣ : type_glob Σ).
   
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
    | wLambda _ _ _ _ => eapply type_Lambda
    | wApp _ _ _ _ => eapply type_App
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
    | HH : ?Σ ;;; ?Γ |-w ?t : _ |- _ ;;; _ |-w ?t : _ =>
      eapply meta_conv; [eapply HH|]
    end
  | |- wf ?Σ ?Γ => first [ assumption | econstructor ]
  | |- _ = _ => first [ reflexivity | now rewrite !lift_lift (* wrong if evars *) | shelve ]
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

Definition type_heq Γ s A a B b :
      wf Σ Γ ->
      Σ ;;; Γ |-w A : wSort s ->
      Σ ;;; Γ |-w B : wSort s ->
      Σ ;;; Γ |-w a : A ->
      Σ ;;; Γ |-w b : B ->
      Σ ;;; Γ |-w wHeq s A a B b : wSort (sum_sort (eq_sort (succ s)) (eq_sort s)).
Proof.
  intros HΓ HA HB Ha Hb; unfold wHeq.
  ittcheck.
Defined.

Definition subst_heq s A a B b n t
  : (wHeq s A a B b){n := t}
    = wHeq s (A{n := t}) (a{n := t}) (B{n := t}) (b{n := t}).
Proof.
  unfold wHeq; cbn -[wcoe].
  rewrite <- !substP2 by omega. cbn -[wcoe].
  rewrite subst_coe. reflexivity.
Defined.

Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
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

Definition type_ProjT2 Γ s A1 A2 p :
    Σ ;;; Γ |-w p : wPack s A1 A2 ->
    Σ ;;; Γ |-w A1 : wSort s ->
    Σ ;;; Γ |-w A2 : wSort s ->
    Σ ;;; Γ |-w wProjT2 s A1 A2 p : A2.
Proof.
  intros H H0 H1; unfold wProjT2; ittcheck. 
  Unshelve. shelve.
  cbn -[wHeq]. substP3.
  rewrite subst_heq. cbn -[wHeq].
  rewrite !lift_lift.
  substP3.
Defined.

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
  - cbn -[wHeq]. substP3.
    rewrite subst_heq. cbn -[wHeq].
    rewrite !lift_lift. substP3.
  - rewrite subst_heq. substP3. apply f_equal.
    cbn -[wHeq]. rewrite !lift00; reflexivity.
Defined.

Ltac other_ittintro t ::=
  lazymatch t with
  | wtransport _ _ _ _ _ _ => eapply type_transport
  | wcoe _ _ _ _ _ => eapply type_coe
  | wHeq _ _ _ _ _ => eapply type_heq
  | wPack _ _ _ => eapply type_Pack
  | wProjT1 _ _ _ _ => eapply type_ProjT1
  | wProjT2 _ _ _ _ => eapply type_ProjT2
  | wProjTe _ _ _ _ => eapply type_ProjTe
  | _ => fail "No introduction rule for" t
  end.

Set Printing Implicit.

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

Definition wcoeβ' A t :=


Definition  type_coeβ' Γ s A t :
    wf Σ Γ ->
    Σ ;;; Γ |-w A : wSort s ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w wcoeβ A t
             : wEq A (wcoe s A A (wRefl (wSort s) A) t) t.
Proof.
  intros H H0 H1; unfold wcoeβ. ittcheck.
  Unshelve.
  cbn; now rewrite substP3, lift00 by omega.
  cbn; now rewrite substP3, lift00 by omega.
Defined.
