(*! Meta-theory for ETT *)

From Coq Require Import Bool String List BinPos Compare_dec ROmega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
               XTyping.

Open Scope x_scope.

Section Conv.

Context `{Sort_notion : Sorts.notion}.

Definition isType (Σ : sglobal_context) (Γ : scontext) (t : sterm) :=
  ∑ s, Σ ;;; Γ |-x t : sSort s.

Inductive xtype_glob : sglobal_context -> Type :=
| xtype_glob_nil : xtype_glob []
| xtype_glob_cons Σ d :
    xtype_glob Σ ->
    fresh_glob (dname d) Σ ->
    isType Σ [] (dtype d) ->
    xtype_glob (d :: Σ).

Derive Signature for type_glob.

Lemma meta_ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-x t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-x t : A.
Proof.
  intros Σ Γ Δ t A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqctx_conv :
  forall {Σ Γ Δ t1 t2 A},
    Σ ;;; Γ |-x t1 = t2 : A ->
    Γ = Δ ->
    Σ ;;; Δ |-x t1 = t2 : A.
Proof.
  intros Σ Γ Δ t1 t2 A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_conv :
  forall {Σ Γ t A B},
    Σ ;;; Γ |-x t : A ->
    A = B ->
    Σ ;;; Γ |-x t : B.
Proof.
  intros Σ Γ t A B h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqconv :
  forall {Σ Γ t t' A B},
    Σ ;;; Γ |-x t = t' : A ->
    A = B ->
    Σ ;;; Γ |-x t = t' : B.
Proof.
  intros Σ Γ t t' A B h e.
  rewrite <- e. exact h.
Defined.

Fixpoint weak_glob_type {Σ Γ t A} (h : Σ ;;; Γ |-x t : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-x t : A

with weak_glob_eq_term {Σ Γ u v A} (h : Σ ;;; Γ |-x u = v : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-x u = v : A

with weak_glob_wf {Σ Γ} (h : wf Σ Γ) :
  forall {d},
    fresh_glob (dname d) Σ ->
    wf (d::Σ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq_term ;
                eassumption
               ).
      eapply type_Ax.
      - eapply weak_glob_wf ; eassumption.
      - cbn. erewrite ident_neq_fresh by eassumption.
        assumption.
    }

  (* weak_glob_eq_term *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq_term ;
                eassumption
               ).
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

Fact typed_ax_type :
  forall {Σ}, xtype_glob Σ ->
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

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-x t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat (erewrite_assumption by romega) ; reflexivity).
  unfold closed_above. 
  case_eq (n <? #|Γ|) ; intro e ; bprop e ; try (zify ; romega).
  reflexivity.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-x t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Fact lift_ax_type :
  forall {Σ},
    xtype_glob Σ ->
    forall {id ty},
      lookup_glob Σ id = Some ty ->
      forall n k, lift n k ty = ty.
Proof.
  intros Σ hg id ty isd n k.
  destruct (typed_ax_type hg isd).
  eapply closed_lift.
  eapply type_ctxempty_closed. eassumption.
Defined.

Fact subst_ax_type :
  forall {Σ},
    xtype_glob Σ ->
    forall {id ty},
      lookup_glob Σ id = Some ty ->
      forall n u, ty{ n := u } = ty.
Proof.
  intros Σ hg id ty isd n k.
  destruct (typed_ax_type hg isd).
  eapply closed_subst.
  eapply type_ctxempty_closed. eassumption.
Defined.

End Conv.

Section Lift.

Context `{Sort_notion : Sorts.notion}.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Ξ |-x t : A ->
          xtype_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-x lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A,
      cong_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Ξ |-x t1 = t2 : A ->
          xtype_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-x lift #|Δ| #|Ξ| t1 = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,,, ?Ξ' |-x _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-x _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-x _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift or cong_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-x ?t : _ |- _ ;;; _ |-x lift _ _ ?t : _ => ih h
  | h : _ ;;; _ |-x ?t = _ : _ |- _ ;;; _ |-x lift _ _ ?t = _ : _ =>
    ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-x t : A) {struct h} :
  xtype_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-x lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with cong_lift {Σ Γ Δ Ξ t1 t2 A} (h : Σ ;;; Γ ,,, Ξ |-x t1 = t2 : A) {struct h} :
  xtype_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-x lift #|Δ| #|Ξ| t1
  = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A

with wf_lift {Σ Γ Δ Ξ} (h : wf Σ (Γ ,,, Ξ)) {struct h} :
  xtype_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)
.
Proof.
  - { dependent destruction h ; intros hΣ hwf.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by (zify ; romega).
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by (zify ; romega).
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_lift ; assumption.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; romega).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. zify ; romega.
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
        eapply type_App ; eih.
      - cbn. eapply type_Sum ; eih.
      - cbn. eapply type_Pair ; eih.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1. reflexivity.
      - cbn. eapply type_Pi1 ; eih.
      - cbn. 
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1. cbn.
        eapply type_Pi2 ; eih.
      - cbn. apply type_Eq ; eih.
      - cbn. eapply type_Refl ; eih.
      - cbn. eapply type_Ax.
        + now apply wf_lift.
        + erewrite lift_ax_type by eassumption. assumption.
      - eapply type_conv ; eih.
    }

  - { intros hg hwf. dependent destruction h.
      - apply eq_reflexivity. apply type_lift ; assumption.
      - apply eq_symmetry. eapply cong_lift ; assumption.
      - eapply eq_transitivity ; eih.
      - change (lift #|Δ| #|Ξ| (t {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t { 0 := u })).
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite 2!substP1. cbn.
        eapply eq_beta ; eih.
      - eapply eq_conv ; eih.
      - cbn. eapply cong_Prod ; eih.
      - cbn. eapply cong_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
        rewrite substP1.
        eapply cong_App ; eih.
      - cbn. eapply cong_Sum ; eih.
      - cbn. eapply cong_Pair ; eih.
        + change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
            with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
          apply substP1.
        + change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
            with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
          apply substP1.
        + change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
            with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
          rewrite <- substP1. reflexivity.
      - cbn. eapply cong_Pi1 ; eih.
      - cbn. 
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite !substP1. cbn.
        eapply cong_Pi2 ; eih.
      - cbn. eapply cong_Eq ; eih.
      - cbn. eapply cong_Refl ; eih.
      - eapply reflection with (e0 := lift #|Δ| #|Ξ| e). eih.
    }

  - { intros hg hwf.
      destruct Ξ.
      - cbn. assumption.
      - dependent destruction h.
        cbn. econstructor.
        + apply wf_lift ; assumption.
        + instantiate (1 := s0). cbn. change (sSort s0) with (lift #|Δ| #|Ξ| (sSort s0)).
          apply type_lift ; assumption.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
       try rewrite lift_context_length ; zify ; romega.

Defined.

End Lift.

Section Subst.

Context `{Sort_notion : Sorts.notion}.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A B u : sterm),
          Σ;;; Γ,, B ,,, Δ |-x t : A ->
          xtype_glob Σ ->
          Σ;;; Γ |-x u : B -> Σ;;; Γ ,,, subst_context u Δ |-x
          t {#|Δ| := u} : A {#|Δ| := u},
     cong_subst :
       forall (Σ : sglobal_context) (Γ Δ : scontext) (t1 t2 A B u : sterm),
         Σ;;; Γ,, B ,,, Δ |-x t1 = t2 : A ->
         xtype_glob Σ ->
         Σ;;; Γ |-x u : B -> Σ;;; Γ ,,, subst_context u Δ |-x
         t1 {#|Δ| := u} = t2 {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-x _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-x _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-x _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst, cong_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-x ?t : _ |- _ ;;; _ |-x ?t{ _ := _ } : _ => sh h
  | h : _ ;;; _ |-x ?t = _ : _ |- _ ;;; _ |-x ?t{ _ := _ } = _ : _ =>
    sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-x t : A) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ |-x u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-x t{ #|Δ| := u } : A{ #|Δ| := u }

with cong_subst {Σ Γ Δ t1 t2 A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-x t1 = t2 : A) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ |-x u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-x t1{ #|Δ| := u }
  = t2{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ B u}
  (h : wf Σ (Γ ,, B ,,, Δ)) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ |-x u : B ->
  wf Σ (Γ ,,, subst_context u Δ)
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by (zify ; romega).
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by (zify ; romega).
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H. intro ge'.
          cbn. rewrite substP3 by (zify ; romega).
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
          * eapply wf_subst ; eassumption.
        + assert (h : n >= #|Δ|) by (zify ; romega).
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try easy.
          rewrite substP3 by (zify ; romega).
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by (zify ; romega).
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel. eapply wf_subst ; eassumption.
          * erewrite safe_nth_ge'.
            f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by (zify ; romega).
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-x _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; zify ; romega)
          end.
          rewrite substP2 by (zify ; romega).
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_subst ; eassumption.
          * f_equal.
            erewrite safe_nth_lt.
            eapply safe_nth_subst_context.
      - cbn. apply type_Sort. eapply wf_subst ; eassumption.
      - cbn. eapply type_Prod ; esh.
      - cbn. eapply type_Lambda ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite substP4. cbn.
        eapply type_App ; esh.
      - cbn. eapply type_Sum ; esh.
      - cbn. eapply type_Pair ; esh.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. reflexivity.
      - cbn. eapply type_Pi1 ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply type_Pi2 ; esh.
      - cbn. eapply type_Eq ; esh.
      - cbn. eapply type_Refl ; esh.
      - cbn. erewrite subst_ax_type by eassumption.
        eapply type_Ax.
        + now eapply wf_subst.
        + assumption.
      - cbn. eapply type_conv ; esh.
    }

  (* cong_subst *)
  - { intros hg hu.
      dependent destruction h.
      - constructor. esh.
      - constructor. esh.
      - eapply eq_transitivity ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply eq_beta ; esh.
      - eapply eq_conv ; esh.
      - cbn. eapply cong_Prod ; esh.
      - cbn. eapply cong_Lambda ; esh.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_App ; esh.
      - cbn. eapply cong_Sum ; esh.
      - cbn. eapply cong_Pair ; esh.
        + change (#|Δ|) with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
        + change (#|Δ|) with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
        + change (#|Δ|) with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
      - cbn. eapply cong_Pi1 ; esh.
      - cbn. 
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_Pi2 ; esh.
      - cbn. eapply cong_Eq ; esh.
      - cbn. eapply cong_Refl ; esh.
      - eapply reflection with (e0 := e{#|Δ| := u}). esh.
    }

  (* wf_subst *)
  - { intros hg hu.
      destruct Δ.
      - cbn. dependent destruction h. assumption.
      - dependent destruction h. cbn. econstructor.
        + eapply wf_subst ; eassumption.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; 
       zify ; romega.
Defined.

End Subst.

Section TypeType.

Context `{Sort_notion : Sorts.notion}.

(* TODO Move *)
Corollary typing_lift01 :
  forall {Σ Γ t A B s},
    xtype_glob Σ ->
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ ,, B |-x lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A B s hg ht hB.
  apply (@type_lift _ _ _ [ B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

(* TODO Move *)
Corollary typing_subst :
  forall {Σ Γ t A B u},
    xtype_glob Σ ->
    Σ ;;; Γ ,, A |-x t : B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Lemma istype_type :
  forall {Σ Γ t T},
    xtype_glob Σ ->
    Σ ;;; Γ |-x t : T ->
    ∑ s, Σ ;;; Γ |-x T : sSort s.
Proof.
  intros Σ Γ t T xhg h.
  induction h.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHw n isdecl') as [s' hh].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - eexists. eapply type_Sort. assumption.
  - eexists. apply type_Sort. eapply typing_wf. eassumption.
  - eexists. eapply type_Prod ; eassumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := u }).
    eapply typing_subst ; eassumption.
  - eexists. econstructor. eapply typing_wf. eassumption.
  - eexists. econstructor ; eassumption.
  - eexists. eassumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := sPi1 A B p }).
    eapply typing_subst ; try eassumption.
    econstructor ; eassumption.
  - eexists. econstructor. eapply typing_wf. eassumption.
  - eexists. econstructor ; eassumption.
  - destruct (typed_ax_type xhg e) as [s hh].
    exists s. change (sSort s) with (lift #|Γ| #|@nil sterm| (sSort s)).
    replace ty with (lift #|Γ| #|@nil sterm| ty)
      by (erewrite lift_ax_type by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - eexists. eassumption.
Defined.

End TypeType.