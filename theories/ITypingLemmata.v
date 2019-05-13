From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Translation
Require Import util SAst SLiftSubst SCommon Equality
               ITyping ITypingInversions.

(* Lemmata about typing *)

Open Scope type_scope.
Open Scope i_scope.

Section Lemmata.

Context `{Sort_notion : Sorts.notion}.

(* Typing up to equality *)
Lemma meta_ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t : A.
Proof.
  intros Σ Γ Δ t A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_conv :
  forall {Σ Γ t A B},
    Σ ;;; Γ |-i t : A ->
    A = B ->
    Σ ;;; Γ |-i t : B.
Proof.
  intros Σ Γ t A B h e.
  rewrite <- e. exact h.
Defined.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat erewrite_assumption ; reflexivity).
  unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try myomega.
  reflexivity.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-i t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

(* TODO: Move the 6 next constructions away. *)
Fact substl_cons :
  forall {a l t}, substl (a :: l) t = (substl l (t{ 0 := a })).
Proof.
  reflexivity.
Defined.

Inductive closed_list : list sterm -> Type :=
| closed_list_nil : closed_list nil
| closed_list_cons a l :
    closed_above #|l| a = true ->
    closed_list l ->
    closed_list (a :: l).

Derive Signature for closed_list.

Fact closed_substl :
  forall {l},
    closed_list l ->
    forall {t},
      closed_above #|l| t = true ->
      closed (substl l t).
Proof.
  intros l cl. induction cl ; intros t h.
  - cbn in *. assumption.
  - rewrite substl_cons. apply IHcl.
    apply closed_above_subst.
    + myomega.
    + assumption.
    + replace (#|l| - 0) with #|l| by myomega. assumption.
Defined.

Fact rev_cons :
  forall {A} {l} {a : A},
    rev (a :: l) = (rev l ++ [a])%list.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [a]). rewrite IHl.
      change (a :: acc) with ([a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_map_cons :
  forall {A B} {f : A -> B} {l} {a : A},
    rev_map f (a :: l) = (rev_map f l ++ [f a])%list.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [f a]). rewrite IHl.
      change (f a :: acc) with ([f a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_length :
  forall {A} {l : list A},
    #|rev l| = #|l|.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- context [ #|?faux _ _| ] => set (aux := faux)
  end.
  assert (h : forall l acc, #|aux l acc| = (#|acc| + #|l|)%nat).
  { intro l. induction l ; intro acc.
    - cbn. myomega.
    - cbn. rewrite IHl. cbn. myomega.
  }
  intro l. apply h.
Defined.

Fact rev_map_length :
  forall {A B} {f : A -> B} {l : list A},
    #|rev_map f l| = #|l|.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- context [ #|?faux _ _| ] => set (aux := faux)
  end.
  assert (h : forall l acc, #|aux l acc| = (#|acc| + #|l|)%nat).
  { intro l. induction l ; intro acc.
    - cbn. myomega.
    - cbn. rewrite IHl. cbn. myomega.
  }
  intro l. apply h.
Defined.

Fact xcomp_lift :
  forall {t}, Xcomp t ->
  forall {n k}, Xcomp (lift n k t).
Proof.
  intros t h. induction h ; intros m k.
  all: try (cbn ; constructor ; easy).
  cbn. destruct (k <=? n) ; constructor.
Defined.

Fact xcomp_subst :
  forall {t}, Xcomp t ->
  forall {u}, Xcomp u ->
  forall {n}, Xcomp (t{ n := u}).
Proof.
  intros t ht. induction ht ; intros t' ht' m.
  all: try (cbn ; constructor; easy).
  cbn. case_eq (m ?= n) ; try constructor.
  intro e. apply xcomp_lift. assumption.
Defined.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq.
  destruct  (string_dec x y); now constructor.
Defined.

Fact ident_neq_fresh :
  forall {Σ id ty d},
    lookup_glob Σ id = Some ty ->
    fresh_glob (dname d) Σ ->
    ident_eq id (dname d) = false.
Proof.
  intro Σ. induction Σ ; intros id ty d h hf.
  - cbn in h. discriminate h.
  - cbn in h. inversion_clear hf.
    unfold ident_eq in *.
    destruct (string_dec id (dname a)).
    destruct (string_dec id (dname d)) ; congruence.
    exact (IHΣ _ _ _ h H).
Defined.

Fixpoint weak_glob_type {Σ Γ t A} (h : Σ ;;; Γ |-i t : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-i t : A

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
      eapply type_Ax.
      - eapply weak_glob_wf ; eassumption.
      - cbn. erewrite ident_neq_fresh by eassumption.
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

Fact xcomp_ax_type :
 forall {Σ}, type_glob Σ ->
  forall {id ty},
    lookup_glob Σ id = Some ty ->
    Xcomp ty.
Proof.
  intros Σ hg. dependent induction hg ; intros id ty h.
  - cbn in h. discriminate h.
  - cbn in h.
    case_eq (ident_eq id (dname d)).
    + intro e. rewrite e in h. inversion h. subst.
      assumption.
    + intro e. rewrite e in h.
      specialize (IHhg _ _ h).
      assumption.
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
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Ξ |-i t : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ : ?T' =>
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
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i lift _ _ ?t : _ => ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-i t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

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
        eapply type_App ; eih.
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
        + cbn. unfold ssnoc. cbn.
          f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by myomega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by myomega.
          change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (sRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_Transport ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        change (lift #|Δ| #|Ξ| (t0 {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t0 { 0 := u })).
        rewrite 2!substP1.
        cbn. eapply type_Beta ; eih.
      - cbn. eapply type_Heq ; eih.
      - cbn. eapply type_HeqToEq ; eih.
      - cbn. eapply type_HeqRefl ; eih.
      - cbn. eapply type_HeqSym ; eih.
      - cbn. eapply @type_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply type_HeqTransport ; eih.
      - cbn. eapply type_CongProd ; try eih.
        cbn. f_equal.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; try eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite 2!substP1.
        eapply type_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongSum ; try eih.
        cbn. f_equal.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongPair ; eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by myomega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * change #|Ξ| with (0 + #|Ξ|)%nat.
            rewrite substP1. reflexivity.
          * change #|Ξ| with (0 + #|Ξ|)%nat.
            rewrite substP1. reflexivity.
        + change #|Ξ| with (0 + #|Ξ|)%nat.
          rewrite substP1. reflexivity.
        + change #|Ξ| with (0 + #|Ξ|)%nat.
          rewrite substP1. reflexivity.
      - cbn. eapply type_CongPi1 ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn.
        change #|Ξ| with (0 + #|Ξ|)%nat.
        rewrite 2!substP1.
        eapply type_CongPi2 ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by myomega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongEq ; eih.
      - cbn. eapply type_CongRefl ; eih.
      - cbn. eapply type_EqToHeq ; eih.
      - cbn. eapply type_HeqTypeEq ; eih.
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
        + instantiate (1 := s0). cbn. change (sSort s0) with (lift #|Δ| #|Ξ| (sSort s0)).
          apply type_lift ; assumption.
    }

    Unshelve.
    all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
      try rewrite lift_context_length ; myomega.
Defined.

Corollary typing_lift01 :
  forall {Σ Γ t A B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, B |-i lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A B s hg ht hB.
  apply (@type_lift _ _ [ B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Corollary typing_lift02 :
  forall {Σ Γ t A B s C s'},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, B |-i C : sSort s' ->
    Σ ;;; Γ ,, B ,, C |-i lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A B s C s' hg ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Fact subst_ax_type :
  forall {Σ},
    type_glob Σ ->
    forall {id ty},
      lookup_glob Σ id = Some ty ->
      forall n u, ty{ n := u } = ty.
Proof.
  intros Σ hg id ty isd n k.
  destruct (typed_ax_type hg isd).
  eapply closed_subst.
  eapply type_ctxempty_closed. eassumption.
Defined.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm)
          (B u : sterm),
          Σ;;; Γ,, B ,,, Δ |-i t : A ->
          type_glob Σ ->
          Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
          t {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i ?t{ _ := _ } : _ => sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ B u}
  (h : wf Σ (Γ ,, B ,,, Δ)) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  wf Σ (Γ ,,, subst_context u Δ)
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by myomega.
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by myomega.
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H0. intro ge'.
          cbn. rewrite substP3 by myomega.
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
          * eapply wf_subst ; eassumption.
        + assert (h : n >= #|Δ|) by myomega.
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try easy.
          rewrite substP3 by myomega.
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by myomega.
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel. eapply wf_subst ; eassumption.
          * erewrite safe_nth_ge'.
            f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by myomega.
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-i _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; myomega)
          end.
          rewrite substP2 by myomega.
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
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by myomega.
        rewrite substP4.
        eapply type_J ; esh.
        + cbn. unfold ssnoc. cbn.
          f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
            apply substP2. myomega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
            apply substP2. myomega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by myomega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by myomega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {0 + #|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply type_Transport ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        change ((t0 {0 := u0}) {#|Δ| := u})
          with ((t0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite 2!substP4. cbn.
        eapply type_Beta ; esh.
      - cbn. eapply type_Heq ; esh.
      - cbn. eapply type_HeqToEq ; esh.
      - cbn. eapply type_HeqRefl ; esh.
      - cbn. eapply type_HeqSym ; esh.
      - cbn.
        eapply type_HeqTrans
          with (B1 := B0{ #|Δ| := u }) (b0 := b{ #|Δ| := u }) ; esh.
      - cbn. eapply type_HeqTransport ; esh.
      - cbn. eapply type_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply type_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongSum ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongPair ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by myomega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * change #|Δ| with (0 + #|Δ|)%nat.
            rewrite substP4. reflexivity.
          * change #|Δ| with (0 + #|Δ|)%nat.
            rewrite substP4. reflexivity.
        + change #|Δ| with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
        + change #|Δ| with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
      - cbn. eapply type_CongPi1 ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply type_CongPi2 ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by myomega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongEq ; esh.
      - cbn. eapply type_CongRefl ; esh.
      - cbn. eapply type_EqToHeq ; esh.
      - cbn. eapply type_HeqTypeEq ; esh.
      - cbn. eapply type_Pack ; esh.
      - cbn. eapply @type_ProjT1 with (A2 := A2{#|Δ| := u}) ; esh.
      - cbn. eapply @type_ProjT2 with (A1 := A1{#|Δ| := u}) ; esh.
      - cbn. eapply type_ProjTe ; esh.
      - cbn. erewrite subst_ax_type by eassumption.
        eapply type_Ax.
        + now eapply wf_subst.
        + assumption.
      - eapply type_rename.
        + esh.
        + eapply nl_subst ; try assumption. reflexivity.
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
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; myomega.
Defined.

Corollary typing_subst :
  forall {Σ Γ t A B u},
    type_glob Σ ->
    Σ ;;; Γ ,, A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Corollary typing_subst2 :
  forall {Σ Γ t A B C u v},
    type_glob Σ ->
    Σ ;;; Γ ,, A ,, B |-i t : C ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Proof.
  intros Σ Γ t A B C u v hg ht hu hv.
  eapply @type_subst with (Δ := []).
  - eapply @type_subst with (Δ := [ B ]).
    + exact ht.
    + assumption.
    + assumption.
  - assumption.
  - cbn. assumption.
Defined.

Inductive typed_list Σ Γ : list sterm -> scontext -> Type :=
| typed_list_nil : typed_list Σ Γ [] []
| typed_list_cons A l Δ T :
    typed_list Σ Γ l Δ ->
    Σ ;;; Γ ,,, Δ |-i A : T ->
    typed_list Σ Γ (A :: l) (Δ ,, T).

Corollary type_substl :
  forall {Σ l Γ Δ},
    type_glob Σ ->
    typed_list Σ Γ l Δ ->
    forall {t T},
      Σ ;;; Γ ,,, Δ |-i t : T ->
      Σ ;;; Γ |-i substl l t : substl l T.
Proof.
  intros Σ l Γ Δ hg tl.
  induction tl ; intros u C h.
  - cbn. assumption.
  - rewrite !substl_cons. apply IHtl.
    eapply typing_subst.
    + assumption.
    + exact h.
    + assumption.
Defined.

Fact substl_sort :
  forall {l s}, substl l (sSort s) = sSort s.
Proof.
  intro l. induction l ; intro s.
  - cbn. reflexivity.
  - rewrite substl_cons. cbn. apply IHl.
Defined.

Fact nth_error_error :
  forall {A} {l : list A} {n},
    nth_error l n = None ->
    n >= #|l|.
Proof.
  intros A l. induction l.
  - intros. cbn. myomega.
  - intros n h. cbn.
    destruct n.
    + cbn in h. inversion h.
    + inversion h as [e].
      specialize (IHl n e).
      myomega.
Defined.

Fact rev_map_nth_error :
  forall {A B} {f : A -> B} {l n a},
    nth_error l n = Some a ->
    nth_error (rev_map f l) (#|l| - S n) = Some (f a).
Proof.
  intros A B f l. induction l ; intros n x hn.
  - destruct n ; inversion hn.
  - destruct n.
    + cbn in hn. inversion hn.
      rewrite rev_map_cons.
      rewrite nth_error_app2.
      * cbn. rewrite rev_map_length.
        replace (#|l| - 0 - #|l|) with 0 by myomega.
        cbn. reflexivity.
      * rewrite rev_map_length. cbn. myomega.
    + cbn in hn.
      rewrite rev_map_cons.
      rewrite nth_error_app1.
      * erewrite IHl by eassumption. reflexivity.
      * rewrite rev_map_length. cbn.
        assert (n < #|l|).
        { apply nth_error_Some. rewrite hn. discriminate. }
        myomega.
Defined.

Fixpoint nlctx Γ :=
  match Γ with
  | A :: Γ => nl A :: nlctx Γ
  | nil => nil
  end.

Lemma nlctx_length :
  forall {Γ Δ},
    nlctx Γ = nlctx Δ ->
    #|Γ| = #|Δ|.
Proof.
  intro Γ. induction Γ ; intros Δ e.
  - cbn. destruct Δ ; simpl in e ; try discriminate e.
    reflexivity.
  - destruct Δ ; simpl in e ; try discriminate e.
    cbn. f_equal. eapply IHΓ.
    simpl in e. inversion e. reflexivity.
Defined.

Lemma nl_safe_nth :
  forall {Γ Δ n i1 i2},
    nlctx Γ = nlctx Δ ->
    nl (safe_nth Δ (exist _ n i1)) = nl (safe_nth Γ (exist _ n i2)).
Proof.
  intros Γ Δ n i1 i2 e. cbn in *. revert Δ n i1 i2 e.
  induction Γ as [| A Γ ih] ; intros Δ n i1 i2 e.
  - cbn. bang.
  - destruct Δ as [|B Δ] ; simpl in e ; try discriminate e.
    inversion e.
    destruct n.
    + cbn. symmetry. assumption.
    + cbn. eapply ih. assumption.
Defined.

Ltac nleq :=
  repeat (try eapply nl_lift ; try eapply nl_subst) ;
  cbn ; auto ; f_equal ; eauto.

Ltac reih :=
  lazymatch goal with
  | h : _ -> _ -> _ -> nl ?t1 = _ -> _ -> _ ;;; _ |-i _ : _,
    e : nl ?t1 = nl ?t2
    |- _ ;;; _ |-i ?t2 : _ =>
    eapply h ; [
      repeat nleq
    | first [ eassumption | reflexivity ]
    | first [
        eassumption
      | econstructor ; try eassumption ; reih
      ]
    ]
  | h : _ -> _ -> _ -> nl ?t = _ -> _ -> _ ;;; _ |-i _ : _
    |- _ ;;; _ |-i ?t : _ =>
    eapply h ; [
      repeat nleq
    | first [ eassumption | reflexivity ]
    | first [
        eassumption
      | econstructor ; try eassumption ; reih
      ]
    ]
  end.

Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-i lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-i ?t { ?n := ?u } : ?S => change S with (S {n := u})
  end.

Lemma rename_typed :
  forall {Σ Γ Δ t u A},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    nlctx Γ = nlctx Δ ->
    nl t = nl u ->
    wf Σ Δ ->
    Σ ;;; Δ |-i u : A.
Proof.
  intros Σ Γ Δ t u A hg h ex e hw. revert Δ ex u e hw.
  induction h ; intros Δ ex t' e hw.
  all: try solve [
    simpl in e ; destruct t' ; try discriminate e ;
    simpl in e ; inversion e ; subst ; clear e ;
    try solve [
          econstructor ; try eassumption ; try reih ;
          try (econstructor ; [ reih | repeat nleq ])
        ] ;
    try solve [
          econstructor ; [
            econstructor ; try eassumption ;
            try reih ;
            try (econstructor ; [ reih | repeat nleq ])
          | repeat nleq
          ]
        ]
  ].
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + unshelve (econstructor ; eassumption).
      rewrite <- (nlctx_length ex). assumption.
    + eapply nl_lift. eapply nl_safe_nth. assumption.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      eapply IHh4.
      * repeat nleq.
      * eassumption.
      * repeat eapply wf_snoc ; try eassumption ; try reih.
        econstructor ; try lift_sort ; try eapply typing_lift01 ;
        try eassumption ; try reih ;
        try (econstructor ; [ reih | repeat nleq ]).
        try econstructor ; [ econstructor |].
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
        -- cbn. nleq.
    + nleq.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh3 ; try eassumption. reflexivity.
           ++ eapply IHh4 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
    + cbn. f_equal.
      all: f_equal.
      all: eauto.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh4 ; try eassumption. reflexivity.
           ++ eapply IHh5 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
      * econstructor.
        -- eapply IHh3.
           ++ repeat nleq.
           ++ assumption.
           ++ repeat eapply wf_snoc ; try eassumption ; try reih.
              econstructor.
              ** eapply IHh4 ; try eassumption. reflexivity.
              ** eapply IHh5 ; try eassumption. reflexivity.
        -- cbn. f_equal.
           all: eapply nl_subst.
           all: try eapply nl_lift.
           all: try reflexivity.
           all: eauto.
    + cbn. f_equal.
      all: f_equal.
      all: eauto.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh5 ; try eassumption. reflexivity.
           ++ eapply IHh6 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
    + cbn. symmetry. f_equal.
      all: try eapply nl_subst.
      all: try assumption.
      all: try reflexivity.
      all: f_equal.
      all: eauto.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh3 ; try eassumption. reflexivity.
           ++ eapply IHh4 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
    + cbn. f_equal.
      all: f_equal.
      all: eauto.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh5 ; try eassumption. reflexivity.
           ++ eapply IHh6 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
    + cbn. f_equal.
      all: f_equal.
      all: eauto.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh4 ; try eassumption. reflexivity.
           ++ eapply IHh5 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
    + cbn. f_equal.
      all: f_equal.
      all: eauto.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      econstructor.
      * eapply IHh2.
        -- repeat nleq.
        -- eassumption.
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
           econstructor.
           ++ eapply IHh4 ; try eassumption. reflexivity.
           ++ eapply IHh5 ; try eassumption. reflexivity.
      * cbn. f_equal.
        all: eapply nl_subst.
        all: try eapply nl_lift.
        all: try reflexivity.
        all: assumption.
    + cbn. symmetry. f_equal.
      all: try eapply nl_subst.
      all: try assumption.
      all: cbn.
      all: f_equal.
      all: eauto.
  - econstructor.
    + eapply IHh ; assumption.
    + assumption.
  Unshelve.
  all: try solve [ constructor ].
  { cbn. auto with arith. }
Defined.

Lemma istype_type :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    exists s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T hg H.
  induction H.
  - revert n isdecl. induction H ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHwf n isdecl') as [s' hh].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - exists (Sorts.succ (Sorts.succ s)). now apply type_Sort.
  - eexists. apply type_Sort. apply (typing_wf H).
  - eexists. apply type_Prod ; eassumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := u }).
    eapply typing_subst ; eassumption.
  - eexists. econstructor. eapply typing_wf. eassumption.
  - eexists. econstructor ; eassumption.
  - eexists. eassumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := sPi1 A B p }).
    eapply typing_subst ; try eassumption.
    econstructor ; eassumption.
  - eexists. apply type_Sort. apply (typing_wf H).
  - eexists. now apply type_Eq.
  - exists s2.
    change (sSort s2) with ((sSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
    + assumption.
    + eassumption.
    + assumption.
    + cbn. rewrite !lift_subst, lift00.
      assumption.
  - eexists. eassumption.
  - destruct IHtyping1 as [z h].
    exists (Sorts.eq_sort z). eapply type_Eq.
    + change (sSort z) with ((sSort z){ 0 := u }).
      eapply typing_subst ; eassumption.
    + eapply type_App ; try eassumption.
      eapply type_Lambda ; eassumption.
    + eapply typing_subst ; eassumption.
  - eexists. apply type_Sort. apply (typing_wf H).
  - eexists. apply type_Eq ; eassumption.
  - eexists. eapply type_Heq ; eassumption.
  - eexists. eapply type_Heq ; eassumption.
  - eexists. eapply type_Heq ; eassumption.
  - eexists. apply type_Heq. all: try eassumption.
    eapply type_Transport ; eassumption.
  - eexists.
    apply type_Heq.
    + eapply type_Sort. apply (typing_wf H).
    + eapply type_Sort. apply (typing_wf H).
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
  - eexists. apply type_Heq.
    + apply type_Prod ; eassumption.
    + apply type_Prod ; assumption.
    + eapply type_Lambda ; eassumption.
    + eapply type_Lambda ; eassumption.
  - eexists. apply type_Heq.
    + lift_sort.
      eapply typing_subst ; eassumption.
    + lift_sort.
      eapply typing_subst ; eassumption.
    + eapply type_App ; eassumption.
    + eapply type_App ; eassumption.
  - eexists.
    apply type_Heq.
    + eapply type_Sort. apply (typing_wf H).
    + eapply type_Sort. apply (typing_wf H).
    + apply type_Sum ; assumption.
    + apply type_Sum ; assumption.
  - eexists. econstructor.
    + econstructor ; eassumption.
    + econstructor ; eassumption.
    + econstructor ; eassumption.
    + econstructor ; eassumption.
  - eexists. econstructor ; try eassumption.
    + econstructor ; eassumption.
    + econstructor ; eassumption.
  - eexists. econstructor ; try eassumption.
    + match goal with
      | |- _ ;;; _ |-i _ { 0 := ?t } : ?S =>
        change S with (S{ 0 := t })
      end.
      eapply typing_subst ; try eassumption.
      econstructor ; eassumption.
    + match goal with
      | |- _ ;;; _ |-i _ { 0 := ?t } : ?S =>
        change S with (S{ 0 := t })
      end.
      eapply typing_subst ; try eassumption.
      econstructor ; eassumption.
    + econstructor ; eassumption.
    + econstructor ; eassumption.
  - eexists. apply type_Heq.
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
  - eexists. apply type_Heq.
    + apply type_Eq ; eassumption.
    + apply type_Eq ; assumption.
    + eapply type_Refl ; eassumption.
    + eapply type_Refl ; eassumption.
  - eexists. eapply type_Heq ; eassumption.
  - eexists. eapply type_Eq ; try assumption.
    apply type_Sort. apply (typing_wf H).
  - eexists. apply type_Sort. apply (typing_wf H).
  - exists s. assumption.
  - exists s. assumption.
  - eexists. apply type_Heq ; try eassumption.
    + eapply type_ProjT1 ; eassumption.
    + eapply @type_ProjT2 with (A1 := A1) ; eassumption.
  - destruct (typed_ax_type hg H0) as [s hh].
    exists s. change (sSort s) with (lift #|Γ| #|@nil sterm| (sSort s)).
    replace ty with (lift #|Γ| #|@nil sterm| ty)
      by (erewrite lift_ax_type by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - destruct IHtyping. eexists.
    eapply rename_typed ; try eassumption.
    + reflexivity.
    + eapply typing_wf. eassumption.
  Unshelve. all: exact nAnon.
Defined.

End Lemmata.
