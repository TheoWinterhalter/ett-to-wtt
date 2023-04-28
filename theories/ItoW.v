From Coq Require Import Bool String List BinPos Compare_dec Lia Arith Utf8.
From Translation Require Import
  util monad_utils Sorts SAst SLiftSubst WAst WLiftSubst SCommon ITyping
  ITypingLemmata WEquality WTyping WChecker WLemmata.
Import ListNotations.

Section Definitions.

  Context {Sort_notion : notion}.

  Fixpoint wLams (l : list wterm) (t : wterm) : wterm :=
    match l with
    | [] => t
    | A :: l => wLambda A (wLams l t)
    end.

  Fixpoint wApps (u : wterm) (l : list wterm) : wterm :=
    match l with
    | [] => u
    | v :: l => wApps (wApp u v) l
    end.

  Fixpoint wProds (l : list wterm) (B : wterm) : wterm :=
    match l with
    | [] => B
    | A :: l => wProd A (wProds l B)
    end.

  Definition wHeq_ctx s := [
    (* A *) wSort s ;
    (* a : A *) wRel 0 ;
    (* B *) wSort s ;
    (* b : B *) wRel 0
  ].

  Definition wHeq s :=
    wLams (wHeq_ctx s) (
      wSum
        (* e : A = B *)
        (wEq (wSort s) (wRel 3) (wRel 1))
        (* transport A B e a = b *)
        (wEq (wRel 2) (wTransport (wRel 4) (wRel 2) (wRel 0) (wRel 3)) (wRel 1))
    ).

  Definition heq_sort s :=
    (sum_sort (eq_sort (succ s)) (eq_sort s)).

End Definitions.

Section Poly.

  (* We use sort polymorphism to use the checker *)
  #[local] Existing Instance psort_notion.

  Lemma ptype_Heq :
    [] ;;; [] |-w wHeq (pvar 0) : wProds (wHeq_ctx (pvar 0)) (wSort (heq_sort (pvar 0))).
  Proof.
    eapply wttinfer_sound. 1: reflexivity. all: constructor.
  Qed.

End Poly.

Section Rules.

  Context {Sort_notion : notion}.

  Lemma type_Heq :
    ∀ s, [] ;;; [] |-w wHeq s : wProds (wHeq_ctx s) (wSort (heq_sort s)).
  Proof.
    intro s.
    pose proof ptype_Heq as h.
    eapply instantiate_sorts_sound with (inst := λ _, s) in h. 2,3: constructor.
    assumption.
  Qed.

End Rules.

Open Scope string_scope.

Section Translation.

  Context {Sort_notion : notion}.

  (* The translation takes an already translated global context *)
  Context (Σ' : wglobal_context).

  (* and an already translated local context *)
  Fixpoint tsl (Γ' : wcontext) (t : sterm) : i_result wterm :=
    match t with
    | sRel n => ret (wRel n)
    | sSort s => ret (wSort s)
    | sProd A B =>
        A' <- tsl Γ' A ;;
        B' <- tsl (Γ' ,, A') B ;;
        ret (wProd A' B')
    | sLambda A B t =>
        A' <- tsl Γ' A ;;
        t' <- tsl (Γ' ,, A') t ;;
        ret (wLambda A' t')
    | sApp u A B v =>
        u' <- tsl Γ' u ;;
        v' <- tsl Γ' v ;;
        ret (wApp u' v')
    | sSum A B =>
        A' <- tsl Γ' A ;;
        B' <- tsl (Γ' ,, A') B ;;
        ret (wSum A' B')
    | sPair A B u v =>
        A' <- tsl Γ' A ;;
        B' <- tsl (Γ' ,, A') B ;;
        u' <- tsl Γ' u ;;
        v' <- tsl Γ' v ;;
        ret (wPair A' B' u' v')
    | sPi1 A B p =>
        A' <- tsl Γ' A ;;
        B' <- tsl (Γ' ,, A') B ;;
        p' <- tsl Γ' p ;;
        ret (wPi1 A' B' p')
    | sPi2 A B p =>
        A' <- tsl Γ' A ;;
        B' <- tsl (Γ' ,, A') B ;;
        p' <- tsl Γ' p ;;
        ret (wPi2 A' B' p')
    | sEq A u v =>
        A' <- tsl Γ' A ;;
        u' <- tsl Γ' u ;;
        v' <- tsl Γ' v ;;
        ret (wEq A' u' v')
    | sRefl A u =>
        A' <- tsl Γ' A ;;
        u' <- tsl Γ' u ;;
        ret (wRefl A' u')
    | sJ A u P w v p =>
        A' <- tsl Γ' A ;;
        u' <- tsl Γ' u ;;
        P' <- tsl (Γ' ,, A' ,, (wEq (lift0 1 A') (lift0 1 u') (wRel 0))) P ;;
        w' <- tsl Γ' w ;;
        v' <- tsl Γ' v ;;
        p' <- tsl Γ' p ;;
        ret (wJ A' u' P' w' v' p')
    | sTransport T1 T2 p t =>
        T1' <- tsl Γ' T1 ;;
        T2' <- tsl Γ' T2 ;;
        p' <- tsl Γ' p ;;
        t' <- tsl Γ' t ;;
        ret (wTransport T1' T2' p' t')
    | sBeta f t =>
        f' <- tsl Γ' f ;;
        t' <- tsl Γ' t ;;
        ret (wBeta f' t')
    | sHeq A a B b =>
        A' <- tsl Γ' A ;;
        a' <- tsl Γ' a ;;
        B' <- tsl Γ' B ;;
        b' <- tsl Γ' b ;;
        s <- getsort =<< wttinfer Σ' Γ' A' ;;
        ret (wApps (wHeq s) [ A' ; a' ; B' ; b' ])
    | sHeqToEq p => ret (wConst "heqtoeq")
    | sHeqRefl A a => ret (wConst "heqrefl")
    | sHeqSym p => ret (wConst "heqsym")
    | sHeqTrans p q => ret (wConst "heqtrans")
    | sHeqTransport p t => ret (wConst "heqtransport")
    | sCongProd B1 B2 pA pB => ret (wConst "congprod")
    | sCongLambda B1 B2 t1 t2 pA pB pt => ret (wConst "conglam")
    | sCongApp B1 B2 pu pA pB pv => ret (wConst "congapp")
    | sCongSum B1 B2 pA pB => ret (wConst "congsum")
    | sCongPair B1 B2 pA pB pu pv => ret (wConst "congpair")
    | sCongPi1 B1 B2 pA pB pp => ret (wConst "congpi1")
    | sCongPi2 B1 B2 pA pB pp => ret (wConst "congpi2")
    | sCongEq pA pu pv => ret (wConst "congeq")
    | sCongRefl pA pu => ret (wConst "congrefl")
    | sEqToHeq p => ret (wConst "eqtoheq")
    | sHeqTypeEq A B p => ret (wConst "heqtypeq")
    | sPack A1 A2 => ret (wConst "pack" (* wPack (tsl Γ' A1) (tsl Γ' A2) *))
    | sProjT1 p => ret (wConst "projT1" (* wProjT1 (tsl Γ' p) *))
    | sProjT2 p => ret (wConst "projT2" (* wProjT2 (tsl Γ' p) *))
    | sProjTe p => ret (wConst "projTe" (* wProjTe (tsl Γ' p) *))
    | sAx id => ret (wConst id)
    end.

  Definition tsl_decl i ty : i_result glob_decl :=
    ty' <- tsl [] ty ;;
    ret {|
      dname := i ;
      dtype := ty' ;
      dbody := None
    |}.

  Fixpoint tsl_ctx (Γ : scontext) : i_result wcontext :=
    match Γ with
    | A :: Γ =>
      Γ' <- tsl_ctx Γ ;;
      A' <- tsl Γ' A ;;
      ret (Γ' ,, A')
    | [] => ret []
    end.

End Translation.

Section MoreTranslation.

  Context {Sort_notion : notion}.

  Fixpoint tsl_glob (Σ : sglobal_context) : i_result wglobal_context :=
    match Σ with
    | d :: Σ =>
      Σ' <- tsl_glob Σ ;;
      d' <- tsl_decl Σ' d.(SCommon.dname) d.(SCommon.dtype) ;;
      ret (d' :: Σ')
    | [] => ret []
    end.

  Open Scope nat_scope.

  (* Lemma tsl_lift :
    ∀ {t n k},
      tsl Γ' (SLiftSubst.lift n k t) = lift n k (tsl Γ' t).
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

Lemma tsl_subst :
  forall {t u n},
    tsl Γ' (t { n := u })%s = (tsl Γ' t){ n := tsl Γ' u }.
Proof.
  intro t. induction t ; intros u m.
  all: try (cbn ; reflexivity).
  all: try (cbn ; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?IHt4, ?IHt5, ?IHt6 ; reflexivity).
  cbn. case_eq (m ?= n) ; intros ; try reflexivity.
  apply tsl_lift.
Defined.

Lemma tsl_lookup :
  forall {Σ id ty},
    SCommon.lookup_glob Σ id = Some ty ->
    lookup_glob (tsl_glob Σ) id = Some (tsl_decl id ty).
Proof.
  intro Σ. induction Σ ; intros id ty he.
  - cbn in he. discriminate he.
  - revert he. cbn. case_eq (ident_eq id (SCommon.dname a)).
    + intros e he. inversion he. subst.
      eapply reflect_iff in e. 2: eapply ident_eq_spec.
      subst. reflexivity.
    + intros e he. eapply IHΣ. assumption.
Defined.

Lemma nth_error_tsl_ctx :
  ∀ Γ n,
    nth_error (tsl_ctx Γ) n = option_map tsl Γ' (nth_error Γ n).
Proof.
  intros Γ n.
  induction Γ as [| ty Γ ih ] in n |- *.
  - simpl. destruct n. all: reflexivity.
  - simpl. destruct n.
    + simpl. reflexivity.
    + simpl. apply ih.
Qed.

Open Scope i_scope.

Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-w lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-w ?t { ?n := ?u } : ?S => change S with (S {n := u})
  end.

Ltac callih :=
  match goal with
  | h : let _ := _ in
        let _ := tsl Γ' ?t in
        let _ := _ in _ -> _ ;;; _ |-w _ : _
    |- _ ;;; _ |-w tsl Γ' ?t : _ =>
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
    let t' := tsl Γ' t in
    let A' := tsl Γ' A in
    type_glob Σ' ->
    wf Σ' Γ' ->
    Σ ;;; Γ |-i t : A ->
    Σ' ;;; Γ' |-w t' : A'.
Proof.
  intros Σ Γ t A Σ' Γ' t' A' hg hw h. induction h.
  all: try solve [go t' A'].
  - unfold t', A'. cbn. rewrite tsl_lift.
    eapply type_Rel.
    + assumption.
    + subst Γ'. rewrite nth_error_tsl_ctx.
      rewrite_assumption. reflexivity.
  - unfold t', A'. cbn. econstructor ; try assumption ; try ih.
    rewrite <- tsl_subst. ih. *)
(*   - unfold t', A'. repeat (rewrite ?tsl_lift, ?tsl_subst). *)
(*     cbn. econstructor ; try assumption ; try ih. *)
(*     + eapply rename_typed ; try assumption. *)
(*       * eapply IHh4. cbn. repeat eapply wf_snoc ; try assumption. *)
(*         -- ih. *)
(*         -- econstructor. *)
(*            ++ rewrite tsl_lift. lift_sort. *)
(*               eapply typing_lift01 ; try assumption ; ih. *)
(*            ++ rewrite 2!tsl_lift. *)
(*               eapply typing_lift01 ; try assumption ; ih. *)
(*            ++ rewrite tsl_lift. refine (type_Rel _ _ _ _ _). *)
(*               ** wfctx ; ih. *)
(*               ** cbn. auto with arith. *)
(*       * cbn. rewrite 2!tsl_lift. reflexivity. *)
(*       * reflexivity. *)
(*       * repeat eapply wf_snoc ; try assumption ; ih. *)
(*         econstructor. *)
(*         -- lift_sort. *)
(*            eapply typing_lift01 ; try assumption ; ih. *)
(*         -- eapply typing_lift01 ; try assumption ; ih. *)
(*         -- refine (type_Rel _ _ _ _ _). *)
(*            ++ wfctx ; ih. *)
(*            ++ cbn. auto with arith. *)
(*     + repeat (rewrite ?tsl_lift, ?tsl_subst in IHh6). ih. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - give_up. *)
(*   - unfold t', A'. econstructor. *)
(*     + assumption. *)
(*     + eapply tsl_lookup. assumption. *)
(*   - eapply type_rename. *)
(*     + eapply IHh. assumption. *)
(*     + unfold A'. eapply nl_tsl. assumption. *)
(* Admitted. *)

(* Lemma tsl_fresh_glob : *)
(*   forall {id Σ}, *)
(*     ITyping.fresh_glob id Σ -> *)
(*     fresh_glob id (tsl_glob Σ). *)
(* Proof. *)
(*   intros id Σ h. induction h. *)
(*   - cbn. constructor. *)
(*   - cbn. econstructor ; assumption. *)
(* Defined. *)

(* Lemma tsl_glob_sound : *)
(*   forall {Σ}, *)
(*     ITyping.type_glob Σ -> *)
(*     type_glob (tsl_glob Σ). *)
(* Proof. *)
(*   intros Σ h. induction h. *)
(*   - cbn. econstructor. *)
(*   - cbn. econstructor ; try assumption. *)
(*     + cbn. eapply tsl_fresh_glob. assumption. *)
(*     + cbn. destruct i as [s hh]. *)
(*       exists s. change (wSort s) with (tsl Γ' (sSort s)). *)
(*       change [] with (tsl_ctx []). *)
(*       eapply tsl_sound ; try assumption. *)
(*       cbn. constructor. *)
(* Defined. *)

(* Lemma tsl_ctx_sound : *)
(*   forall {Σ Γ}, *)
(*     ITyping.type_glob Σ -> *)
(*     ITyping.wf Σ Γ -> *)
(*     wf (tsl_glob Σ) (tsl_ctx Γ). *)
(* Proof. *)
(*   intros Σ Γ hg hw. induction hw. *)
(*   - cbn. constructor. *)
(*   - cbn. econstructor ; try eassumption. *)
(*     match goal with *)
(*     | |- _ ;;; _ |-w _ : wSort ?s => *)
(*       change (wSort s) with (tsl Γ' (sSort s)) *)
(*     end. *)
(*     eapply tsl_sound ; try eassumption. *)
(*     eapply tsl_glob_sound. assumption. *)
(* Defined. *)

(* Corollary tsl_soundness : *)
(* forall {Σ Γ t A}, *)
(*     let Σ' := tsl_glob Σ in *)
(*     let Γ' := tsl_ctx Γ in *)
(*     let t' := tsl Γ' t in *)
(*     let A' := tsl Γ' A in *)
(*     ITyping.type_glob Σ -> *)
(*     Σ ;;; Γ |-i t : A -> *)
(*     Σ' ;;; Γ' |-w t' : A'. *)
(* Proof. *)
(*   intros Σ Γ t A Σ' Γ' t' A' hg h. *)
(*   eapply tsl_sound ; try assumption. *)
(*   - eapply tsl_glob_sound. assumption. *)
(*   - eapply tsl_ctx_sound ; try assumption. *)
(*     eapply ITypingLemmata.typing_wf. eassumption. *)
(* Defined. *)

End MoreTranslation.
