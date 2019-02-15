From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util WAst WLiftSubst WTyping.

Section Lemmata.

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
(* Proof. *)
(*   - { dependent destruction h ; intros hΣ hwf. *)
(*       - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e. *)
(*         + rewrite liftP3 by myomega. *)
(*           replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by myomega. *)
(*           eapply meta_conv. *)
(*           * eapply type_Rel. *)
(*             eapply wf_lift ; assumption. *)
(*           * f_equal. f_equal. *)
(*             erewrite 3!safe_nth_ge' *)
(*               by (try rewrite lift_context_length ; myomega). *)
(*             eapply safe_nth_cong_irr. *)
(*             rewrite lift_context_length. myomega. *)
(*         + eapply meta_conv. *)
(*           * eapply type_Rel. eapply wf_lift ; assumption. *)
(*           * erewrite 2!safe_nth_lt. *)
(*             eapply lift_context_ex. *)
(*       - cbn. apply type_Sort. now apply wf_lift. *)
(*       - cbn. eapply type_Prod ; eih. *)
(*       - cbn. eapply type_Lambda ; eih. *)
(*       - cbn. *)
(*         change (lift #|Δ| #|Ξ| (B {0 := u})) *)
(*           with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })). *)
(*         rewrite substP1. *)
(*         eapply type_App ; eih. *)
(*       - cbn. eapply type_Sum ; eih. *)
(*       - cbn. eapply type_Pair ; eih. *)
(*         change (#|Ξ|) with (0 + #|Ξ|)%nat. *)
(*         rewrite substP1. reflexivity. *)
(*       - cbn. eapply type_Pi1 ; eih. *)
(*       - cbn. *)
(*         change (#|Ξ|) with (0 + #|Ξ|)%nat. *)
(*         rewrite substP1. cbn. *)
(*         eapply type_Pi2 ; eih. *)
(*       - cbn. apply type_Eq ; eih. *)
(*       - cbn. eapply type_Refl ; eih. *)
(*       - change (#|Ξ|) with (0 + #|Ξ|)%nat. *)
(*         rewrite substP1. *)
(*         replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by myomega. *)
(*         rewrite substP1. *)
(*         cbn. eapply type_J ; try eih. *)
(*         + cbn. unfold ssnoc. cbn. *)
(*           f_equal. f_equal. *)
(*           * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega. *)
(*             apply liftP2. myomega. *)
(*           * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega. *)
(*             apply liftP2. myomega. *)
(*         + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by myomega. *)
(*           rewrite <- substP1. *)
(*           replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by myomega. *)
(*           change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u)) *)
(*             with (lift #|Δ| #|Ξ| (sRefl A0 u)). *)
(*           rewrite <- substP1. reflexivity. *)
(*       - cbn. eapply type_Transport ; eih. *)
(*       - cbn. eapply type_Heq ; eih. *)
(*       - cbn. eapply type_HeqToEq ; eih. *)
(*       - cbn. eapply type_HeqRefl ; eih. *)
(*       - cbn. eapply type_HeqSym ; eih. *)
(*       - cbn. eapply @type_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih. *)
(*       - cbn. eapply type_HeqTransport ; eih. *)
(*       - cbn. eapply type_CongProd ; try eih. *)
(*         cbn. f_equal. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*       - cbn. eapply type_CongLambda ; try eih. *)
(*         + cbn. f_equal. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*         + cbn. f_equal. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*       - cbn. *)
(*         change (lift #|Δ| #|Ξ| (B1 {0 := v1})) *)
(*           with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })). *)
(*         change (lift #|Δ| #|Ξ| (B2 {0 := v2})) *)
(*           with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })). *)
(*         rewrite 2!substP1. *)
(*         eapply type_CongApp ; eih. *)
(*         cbn. f_equal. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*       - cbn. eapply type_CongSum ; try eih. *)
(*         cbn. f_equal. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*       - cbn. eapply type_CongPair ; eih. *)
(*         + cbn. f_equal. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*           * rewrite <- liftP2 by myomega. *)
(*             change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*             rewrite substP1. cbn. reflexivity. *)
(*         + cbn. f_equal. *)
(*           * change #|Ξ| with (0 + #|Ξ|)%nat. *)
(*             rewrite substP1. reflexivity. *)
(*           * change #|Ξ| with (0 + #|Ξ|)%nat. *)
(*             rewrite substP1. reflexivity. *)
(*         + change #|Ξ| with (0 + #|Ξ|)%nat. *)
(*           rewrite substP1. reflexivity. *)
(*         + change #|Ξ| with (0 + #|Ξ|)%nat. *)
(*           rewrite substP1. reflexivity. *)
(*       - cbn. eapply type_CongPi1 ; eih. *)
(*         cbn. f_equal. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*       - cbn. *)
(*         change #|Ξ| with (0 + #|Ξ|)%nat. *)
(*         rewrite 2!substP1. *)
(*         eapply type_CongPi2 ; eih. *)
(*         cbn. f_equal. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*         + rewrite <- liftP2 by myomega. *)
(*           change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1. *)
(*           rewrite substP1. cbn. reflexivity. *)
(*       - cbn. eapply type_CongEq ; eih. *)
(*       - cbn. eapply type_CongRefl ; eih. *)
(*       - cbn. eapply type_EqToHeq ; eih. *)
(*       - cbn. eapply type_HeqTypeEq ; eih. *)
(*       - cbn. eapply type_Pack ; eih. *)
(*       - cbn. eapply @type_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih. *)
(*       - cbn. eapply @type_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih. *)
(*       - cbn. eapply type_ProjTe ; eih. *)
(*       - cbn. erewrite lift_ax_type by eassumption. *)
(*         eapply type_Ax. *)
(*         + now apply wf_lift. *)
(*         + assumption. *)
(*       - eapply type_conv ; try eih. *)
(*         eapply lift_conv. assumption. *)
(*     } *)

(*   (* wf_lift *) *)
(*   - { intros hg hwf. *)
(*       destruct Ξ. *)
(*       - cbn. assumption. *)
(*       - dependent destruction h. *)
(*         cbn. econstructor. *)
(*         + apply wf_lift ; assumption. *)
(*         + instantiate (1 := s0). cbn. change (sSort s0) with (lift #|Δ| #|Ξ| (sSort s0)). *)
(*           apply type_lift ; assumption. *)
(*     } *)

(*     Unshelve. *)
(*     all: try rewrite !length_cat ; try rewrite length_cat in isdecl ; *)
(*       try rewrite lift_context_length ; myomega. *)
(* Defined. *)
Admitted.

End Lemmata.