
From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template
Require Import Ast utils monad_utils Typing Checker.
From Translation
     Require Import util Sorts SAst SLiftSubst WAst WLiftSubst
     SCommon ITyping ITypingLemmata
     WTyping WChecker WLemmata Quotes.
From TypingFlags Require Import Loader.
Import MonadNotation ListNotations.

Section s.
Context (Sort_notion : notion).

Fixpoint tsl (t : sterm) : wterm :=
  match t with
  | sRel n => wRel n
  | sSort s => wSort s
  | sProd nx A B => wProd nx (tsl A) (tsl B)
  | sLambda nx A B t => wLambda nx (tsl A) (tsl t)
  | sApp u A B v => wApp (tsl u) (tsl v)
  | sSum nx A B => wSum nx (tsl A) (tsl B)
  | sPair A B u v => wPair (tsl A) (tsl B) (tsl u) (tsl v)
  | sPi1 A B p => wPi1 (tsl A) (tsl B) (tsl p)
  | sPi2 A B p => wPi2 (tsl A) (tsl B) (tsl p)
  | sEq A u v => wEq (tsl A) (tsl u) (tsl v)
  | sRefl A u => wRefl (tsl A) (tsl u)
  | sJ A u P w v p => wJ (tsl A) (tsl u) (tsl P) (tsl w) (tsl v) (tsl p)
  | sTransport T1 T2 p t => wTransport (tsl T1) (tsl T2) (tsl p) (tsl t)
  | sBeta f t => wBeta (tsl f) (tsl t)
  | sHeq A a B b => wHeq (tsl A) (tsl a) (tsl B) (tsl b)
  (* | sHeqToEq p => _ *)
  (* | sHeqRefl A a => _ *)
  (* | sHeqSym p => _ *)
  (* | sHeqTrans p q => _ *)
  (* | sHeqTransport p t => _ *)
  (* | sCongProd B1 B2 pA pB => _ *)
  (* | sCongLambda B1 B2 t1 t2 pA pB pt => _ *)
  (* | sCongApp B1 B2 pu pA pB pv => _ *)
  (* | sCongSum B1 B2 pA pB => _ *)
  (* | sCongPair B1 B2 pA pB pu pv => _ *)
  (* | sCongPi1 B1 B2 pA pB pp => _ *)
  (* | sCongPi2 B1 B2 pA pB pp => _ *)
  (* | sCongEq pA pu pv => _ *)
  (* | sCongRefl pA pu => _ *)
  (* | sEqToHeq p => _ *)
  (* | sHeqTypeEq A B p => _ *)
  (* | sPack A1 A2 => _ *)
  (* | sProjT1 p => _ *)
  (* | sProjT2 p => _ *)
  (* | sProjTe p => _ *)
  (* | sAx id => _ *)
  | _ => wAx "todo"
  end.

Fixpoint tsl_glob (Σ : sglobal_context) : wglobal_context :=
  match Σ with
  | d :: Σ =>
    {| dname := d.(SCommon.dname) ; dtype := tsl d.(SCommon.dtype) |}
    :: tsl_glob Σ
  | nil => nil
  end.

Fixpoint tsl_ctx (Γ : scontext) : wcontext :=
  match Γ with
  | A :: Γ => tsl A :: tsl_ctx Γ
  | nil => nil
  end.

Lemma tsl_lift :
  forall {t n k},
    tsl (SLiftSubst.lift n k t) = lift n k (tsl t).
Proof.
  intro t. induction t ; intros m k.
  all: try (cbn ; reflexivity).
  all: try (cbn ; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?IHt4, ?IHt5, ?IHt6 ; reflexivity).
  cbn. case_eq (k <=? n) ; intros ; reflexivity.
Defined.

Lemma tsl_ctx_length :
  forall {Γ},
    #|tsl_ctx Γ| = #|Γ|.
Proof.
  intro Γ. induction Γ ; eauto.
  cbn. f_equal. assumption.
Defined.

Lemma tsl_safe_nth :
  forall {Γ n i1 i2},
    tsl (safe_nth Γ (exist _ n i1)) = safe_nth (tsl_ctx Γ) (exist _ n i2).
Proof.
  intros Γ. induction Γ ; intros n i1 i2.
  - cbn in i1. omega.
  - destruct n.
    + cbn. reflexivity.
    + cbn. erewrite IHΓ. reflexivity.
Defined.

Lemma tsl_subst :
  forall {t u n},
    tsl (t { n := u })%s = (tsl t){ n := tsl u }.
Proof.
  intro t. induction t ; intros u m.
  all: try (cbn ; reflexivity).
  all: try (cbn ; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?IHt4, ?IHt5, ?IHt6 ; reflexivity).
  cbn. case_eq (m ?= n) ; intros ; try reflexivity.
  apply tsl_lift.
Defined.

Open Scope i_scope.

Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-w lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-w ?t { ?n := ?u } : ?S => change S with (S {n := u})
  end.

Ltac callih :=
  match goal with
  | h : let _ := _ in
        let _ := tsl ?t in
        let _ := _ in _ -> _ ;;; _ |-w _ : _
    |- _ ;;; _ |-w tsl ?t : _ =>
    eapply h
  end.

Ltac wfctx :=
  first [
    eassumption
    | cbn ; eapply wf_snoc ; try assumption
  ].

Ltac ih :=
  repeat (callih ; wfctx).

Ltac go t' A' :=
  unfold t', A' ; cbn ;
  repeat (rewrite ?tsl_lift, ?tsl_subst) ;
  econstructor ; try assumption ; ih.

Lemma tsl_sound :
  forall {Σ Γ t A},
    let Σ' := tsl_glob Σ in
    let Γ' := tsl_ctx Γ in
    let t' := tsl t in
    let A' := tsl A in
    type_glob Σ' ->
    wf Σ' Γ' ->
    Σ ;;; Γ |-i t : A ->
    Σ' ;;; Γ' |-w t' : A'.
Proof.
  intros Σ Γ t A Σ' Γ' t' A' hg hw h. induction h.
  all: try solve [go t' A'].
  - unfold t', A'. cbn. rewrite tsl_lift. unshelve erewrite tsl_safe_nth.
    + cbn. rewrite tsl_ctx_length. assumption.
    + econstructor. assumption.
  - unfold t', A'. cbn. econstructor ; try assumption ; try ih.
    rewrite <- tsl_subst. ih.
  - unfold t', A'. repeat (rewrite ?tsl_lift, ?tsl_subst).
    cbn. econstructor ; try assumption ; try ih.
    + eapply rename_typed ; try assumption.
      * eapply IHh4. cbn. repeat eapply wf_snoc ; try assumption.
        -- ih.
        -- econstructor.
           ++ rewrite tsl_lift. lift_sort.
              eapply typing_lift01 ; try assumption ; ih.
           ++ rewrite 2!tsl_lift.
              eapply typing_lift01 ; try assumption ; ih.
           ++ rewrite tsl_lift. refine (type_Rel _ _ _ _ _).
              ** wfctx ; ih.
              ** cbn. auto with arith.
      * cbn. rewrite 2!tsl_lift. reflexivity.
      * reflexivity.
      * repeat eapply wf_snoc ; try assumption ; ih.
        econstructor.
        -- lift_sort.
           eapply typing_lift01 ; try assumption ; ih.
        -- eapply typing_lift01 ; try assumption ; ih.
        -- refine (type_Rel _ _ _ _ _).
           ++ wfctx ; ih.
           ++ cbn. auto with arith.
    + repeat (rewrite ?tsl_lift, ?tsl_subst in IHh6). ih.
  - unfold t', A'. repeat (rewrite ?tsl_lift, ?tsl_subst).
    (* cbn. econstructor ; try assumption ; try ih. *)
    admit.
    (* Reached the TODO point *)
Admitted.

Lemma tsl_fresh_glob :
  forall {id Σ},
    ITyping.fresh_glob id Σ ->
    fresh_glob id (tsl_glob Σ).
Proof.
  intros id Σ h. induction h.
  - cbn. constructor.
  - cbn. econstructor ; assumption.
Defined.

Lemma tsl_glob_sound :
  forall {Σ},
    ITyping.type_glob Σ ->
    type_glob (tsl_glob Σ).
Proof.
  intros Σ h. induction h.
  - cbn. econstructor.
  - cbn. econstructor ; try assumption.
    + cbn. eapply tsl_fresh_glob. assumption.
    + cbn. destruct i as [s hh].
      exists s. change (wSort s) with (tsl (sSort s)).
      change [] with (tsl_ctx []).
      eapply tsl_sound ; try assumption.
      cbn. constructor.
Defined.

Lemma tsl_ctx_sound :
  forall {Σ Γ},
    ITyping.type_glob Σ ->
    ITyping.wf Σ Γ ->
    wf (tsl_glob Σ) (tsl_ctx Γ).
Proof.
  intros Σ Γ hg hw. induction hw.
  - cbn. constructor.
  - cbn. econstructor ; try eassumption.
    match goal with
    | |- _ ;;; _ |-w _ : wSort ?s =>
      change (wSort s) with (tsl (sSort s))
    end.
    eapply tsl_sound ; try eassumption.
    eapply tsl_glob_sound. assumption.
Defined.

Corollary tsl_soundness :
forall {Σ Γ t A},
    let Σ' := tsl_glob Σ in
    let Γ' := tsl_ctx Γ in
    let t' := tsl t in
    let A' := tsl A in
    ITyping.type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ' ;;; Γ' |-w t' : A'.
Proof.
  intros Σ Γ t A Σ' Γ' t' A' hg h.
  eapply tsl_sound ; try assumption.
  - eapply tsl_glob_sound. assumption.
  - eapply tsl_ctx_sound ; try assumption.
    eapply ITypingLemmata.typing_wf. eassumption.
Defined.

End s.