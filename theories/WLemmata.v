From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util WAst WLiftSubst WTyping WEquality.

Section Lemmata.

Open Scope w_scope.

Context `{Sort_notion : Sorts.notion}.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-w t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Fixpoint lift_context n Γ : wcontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift n #|Γ| A) :: (lift_context n Γ)
  end.

Lemma lift_context_length :
  forall Γ n, #|lift_context n Γ| = #|Γ|.
Proof.
  intro Γ. induction Γ ; intro m.
  - reflexivity.
  - cbn. f_equal. eapply IHΓ.
Defined.

Fact safe_nth_lift_context :
  forall {Γ Δ : wcontext} {n isdecl isdecl'},
    safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl) =
    lift #|Γ| (#|Δ| - n - 1) (safe_nth Δ (exist _ n isdecl')).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. intros. bang.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by myomega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : wcontext} {n isdecl isdecl'},
    lift0 (S n) (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl)) =
    lift #|Δ| #|Ξ| (lift0 (S n) (safe_nth Ξ (exist _ n isdecl'))).
Proof.
  intros Δ Ξ n isdecl isdecl'.
  erewrite safe_nth_lift_context.
  rewrite <- liftP2 by myomega.
  cbn.
  replace (S (n + (#|Ξ| - n - 1)))%nat with #|Ξ|.
  - reflexivity.
  - revert n isdecl isdecl'. induction Ξ ; intros n isdecl isdecl'.
    + cbn. exfalso. abstract easy.
    + cbn. f_equal.
      destruct n.
      * cbn. myomega.
      * cbn. apply IHΞ.
        -- cbn in *. myomega.
        -- cbn in *. myomega.
Defined.

Definition wapp_context (Γ Γ' : wcontext) : wcontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " :=
  (wapp_context Γ Γ')
    (at level 25, Γ' at next level, left associativity) : w_scope.

Lemma meta_conv :
  forall Σ Γ t A B,
    Σ ;;; Γ |-w t : A ->
    A = B ->
    Σ ;;; Γ |-w t : B.
Proof.
  intros Σ Γ t A B h e.
  destruct e. assumption.
Defined.

Lemma meta_ctx_conv :
  forall Σ Γ Δ t A,
    Σ ;;; Γ |-w t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-w t : A.
Proof.
  intros Σ Γ Δ t A H e.
  destruct e. assumption.
Defined.

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

Fact safe_nth_S :
  forall {A n} {a : A} {l isdecl},
    ∑ isdecl',
      safe_nth (a :: l) (exist _ (S n) isdecl) =
      safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intros a l isdecl.
  - cbn. eexists. reflexivity.
  - eexists. cbn. reflexivity.
Defined.

Lemma eq_safe_nth' :
  forall {Γ : wcontext} {n a isdecl isdecl'},
    safe_nth (a :: Γ) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n A isdecl isdecl'.
  - exfalso. abstract easy.
  - destruct n.
    + reflexivity.
    + destruct (@safe_nth_S _ (S n) A (a :: Γ) isdecl')
        as [isecl0 eq].
      rewrite eq.
      destruct (@safe_nth_S _ n a Γ isdecl)
        as [isecl1 eq1].
      rewrite eq1.
      apply IHΓ.
Defined.

Lemma eq_safe_nth :
  forall {Γ : wcontext} {n A isdecl isdecl'},
    safe_nth (Γ ,, A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n A isdecl isdecl'.
  apply eq_safe_nth'.
Defined.

Fact safe_nth_irr :
  forall {A n} {l : list A} {isdecl isdecl'},
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intro l ; destruct l ; intros isdecl isdecl'.
  all: cbn. all: try bang.
  - reflexivity.
  - eapply IHn.
Defined.

Fact safe_nth_cong_irr :
  forall {A n m} {l : list A} {isdecl isdecl'},
    n = m ->
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ m isdecl').
Proof.
  intros A n m l isdecl isdecl' e.
  revert isdecl isdecl'.
  rewrite e. intros isdecl isdecl'.
  apply safe_nth_irr.
Defined.

Fact safe_nth_ge :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n - #|Δ| < #|Γ| },
    n >= #|Δ| ->
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) isdecl').
Proof.
  intros Γ Δ.
  induction Δ ; intros n isdecl isdecl' h.
  - cbn in *. revert isdecl'.
    replace (n - 0) with n by myomega.
    intros isdecl'. apply safe_nth_irr.
  - destruct n.
    + cbn in *. inversion h.
    + cbn. apply IHΔ. cbn in *. myomega.
Defined.

Definition ge_sub {Γ Δ n} (isdecl : n < #|Γ ,,, Δ|) :
  n >= #|Δ| ->  n - #|Δ| < #|Γ|.
Proof.
  intro h.
  rewrite length_cat in isdecl. myomega.
Defined.

Fact safe_nth_ge' :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } (h : n >= #|Δ|),
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) (ge_sub isdecl h)).
Proof.
  intros Γ Δ n isdecl h.
  eapply safe_nth_ge. assumption.
Defined.

Fact safe_nth_lt :
  forall {n Γ Δ} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n < #|Δ| },
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Δ (exist _ n isdecl').
Proof.
  intros n. induction n ; intros Γ Δ isdecl isdecl'.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. reflexivity.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. eapply IHn.
Defined.

Fact ident_neq_fresh :
  forall {Σ id ty d},
    lookup_glob Σ id = Some ty ->
    fresh_glob (dname d) Σ ->
    ident_eq id (dname d) = false.
Proof.
  intro Σ. induction Σ ; intros id ty d h hf.
  - cbn in h. discriminate h.
  - cbn in h. dependent destruction hf.
    case_eq (ident_eq id (dname d0)) ;
    intro e ; rewrite e in h.
    + inversion h as [ h' ]. subst. clear h.
      destruct (ident_eq_spec id (dname d)).
      * subst. destruct (ident_eq_spec (dname d) (dname d0)).
        -- exfalso. easy.
        -- easy.
      * reflexivity.
    + eapply IHΣ ; eassumption.
Defined.

Fixpoint weak_glob_type {Σ Γ t A} (h : Σ ;;; Γ |-w t : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-w t : A

with weak_glob_wf {Σ Γ} (h : wf Σ Γ) :
  forall {d},
    fresh_glob (dname d) Σ ->
    wf (d::Σ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                eassumption
               ).
      - eapply type_ProjT2 with (A3 := A1).
        all: apply weak_glob_type ; eassumption.
      - eapply type_Ax.
        + eapply weak_glob_wf ; eassumption.
        + cbn. erewrite ident_neq_fresh by eassumption.
          assumption.
    }

  (* weak_glob_wf *)
  - { dependent destruction h ; intros fd.
      - constructor.
      - econstructor.
        + apply weak_glob_wf ; assumption.
        + apply weak_glob_type ; eassumption.
    }
Defined.

Corollary weak_glob_isType :
  forall {Σ Γ A} (h : isType Σ Γ A) {d},
    fresh_glob (dname d) Σ ->
    isType (d::Σ) Γ A.
Proof.
  intros Σ Γ A h d hf.
  destruct h as [s h].
  exists s. eapply weak_glob_type ; eassumption.
Defined.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-w t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat erewrite_assumption ; reflexivity).
  unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try myomega.
  reflexivity.
Defined.

Fact typed_ax_type :
  forall {Σ}, type_glob Σ ->
  forall {id ty},
    lookup_glob Σ id = Some ty ->
    isType Σ [] ty.
Proof.
  intros Σ hg. dependent induction hg ; intros id ty h.
  - cbn in h. discriminate h.
  - cbn in h.
    case_eq (ident_eq id (dname d)).
    + intro e. rewrite e in h. inversion h. subst.
      eapply weak_glob_isType ; eassumption.
    + intro e. rewrite e in h.
      specialize (IHhg _ _ h).
      eapply weak_glob_isType ; eassumption.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-w t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Fact lift_ax_type :
  forall {Σ},
    type_glob Σ ->
    forall {id ty},
      lookup_glob Σ id = Some ty ->
      forall n k, lift n k ty = ty.
Proof.
  intros Σ hg id ty isd n k.
  destruct (typed_ax_type hg isd).
  eapply closed_lift.
  eapply type_ctxempty_closed. eassumption.
Defined.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : wglobal_context) (Γ Δ Ξ : wcontext) (t A : wterm),
          Σ;;; Γ ,,, Ξ |-w t : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-w lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-w ?t : _ |- _ ;;; _ |-w lift _ _ ?t : _ => ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-w t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-w lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with wf_lift {Σ Γ Δ Ξ} (h : wf Σ (Γ ,,, Ξ)) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)
.
Proof.
  - { dependent destruction h ; intros hΣ hwf.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by myomega.
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by myomega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_lift ; assumption.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; myomega).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. myomega.
        + eapply meta_conv.
          * eapply type_Rel. eapply wf_lift ; assumption.
          * erewrite 2!safe_nth_lt.
            eapply lift_context_ex.
      - cbn. apply type_Sort. now apply wf_lift.
      - cbn. eapply type_Prod ; eih.
      - cbn. eapply type_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1.
        eapply type_App with (A := lift #|Δ| #|Ξ| A0) ; eih.
      - cbn. eapply type_Sum ; eih.
      - cbn. eapply type_Pair ; eih.
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1. reflexivity.
      - cbn. eapply type_Pi1 ; eih.
      - cbn.
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1. cbn.
        eapply type_Pi2 ; eih.
      - cbn. apply type_Eq ; eih.
      - cbn. eapply type_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by myomega.
        rewrite substP1.
        cbn. eapply type_J ; try eih.
        + cbn. unfold snoc. cbn.
          f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by myomega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by myomega.
          change (wRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (wRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_Transport ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        change (lift #|Δ| #|Ξ| (t0 {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t0 { 0 := u })).
        rewrite 2!substP1.
        eapply type_Beta ; eih.
      - cbn. eapply type_K ; eih.
      - cbn. eapply type_Funext ; eih.
        cbn. f_equal. f_equal.
        + f_equal. replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
        + f_equal. replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
      - cbn. eapply type_Heq ; eih.
      - cbn. eapply type_HeqPair ; eih.
      - cbn. eapply type_HeqTy ; eih.
      - cbn. eapply type_HeqTm ; eih.
      - cbn. eapply type_Pack ; eih.
      - cbn. eapply @type_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply @type_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply type_ProjTe ; eih.
      - cbn. erewrite lift_ax_type by eassumption.
        eapply type_Ax.
        + now apply wf_lift.
        + assumption.
      - eapply type_rename.
        + eih.
        + eapply nl_lift. assumption.
    }

  (* wf_lift *)
  - { intros hg hwf.
      destruct Ξ.
      - cbn. assumption.
      - dependent destruction h.
        cbn. econstructor.
        + apply wf_lift ; assumption.
        + instantiate (1 := s). cbn. change (wSort s) with (lift #|Δ| #|Ξ| (wSort s)).
          apply type_lift ; assumption.
    }

    Unshelve.
    all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
      try rewrite lift_context_length ; myomega.
Defined.

Corollary typing_lift01 :
  forall {Σ Γ t A B s},
    type_glob Σ ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ ,, B |-w lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A B s hg ht hB.
  apply (@type_lift _ _ [ B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

End Lemmata.