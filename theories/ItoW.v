From Coq Require Import Bool String List BinPos Compare_dec Lia Arith Utf8.
From Translation Require Import
  util Sorts SAst SLiftSubst WAst WLiftSubst SCommon ITyping ITypingLemmata
  WTyping WChecker WLemmata.
Import ListNotations.
Open Scope string_scope.

Section Translation.

Context (Sort_notion : notion).

(* Note we will require Σ and Γ in order to do some inference
   meaning we will also land in a monad.
 *)
Fixpoint tsl (t : sterm) : wterm :=
  match t with
  | sRel n => wRel n
  | sSort s => wSort s
  | sProd A B => wProd (tsl A) (tsl B)
  | sLambda A B t => wLambda (tsl A) (tsl t)
  | sApp u A B v => wApp (tsl u) (tsl v)
  | sSum A B => wSum (tsl A) (tsl B)
  | sPair A B u v => wPair (tsl A) (tsl B) (tsl u) (tsl v)
  | sPi1 A B p => wPi1 (tsl A) (tsl B) (tsl p)
  | sPi2 A B p => wPi2 (tsl A) (tsl B) (tsl p)
  | sEq A u v => wEq (tsl A) (tsl u) (tsl v)
  | sRefl A u => wRefl (tsl A) (tsl u)
  | sJ A u P w v p => wJ (tsl A) (tsl u) (tsl P) (tsl w) (tsl v) (tsl p)
  | sTransport T1 T2 p t => wTransport (tsl T1) (tsl T2) (tsl p) (tsl t)
  | sBeta f t => wBeta (tsl f) (tsl t)
  | sHeq A a B b => wConst "heq" (* wHeq (tsl A) (tsl a) (tsl B) (tsl b) *)
  | sHeqToEq p => wConst "heqtoeq"
  | sHeqRefl A a => wConst "heqrefl"
  | sHeqSym p => wConst "heqsym"
  | sHeqTrans p q => wConst "heqtrans"
  | sHeqTransport p t => wConst "heqtransport"
  | sCongProd B1 B2 pA pB => wConst "congprod"
  | sCongLambda B1 B2 t1 t2 pA pB pt => wConst "conglam"
  | sCongApp B1 B2 pu pA pB pv => wConst "congapp"
  | sCongSum B1 B2 pA pB => wConst "congsum"
  | sCongPair B1 B2 pA pB pu pv => wConst "congpair"
  | sCongPi1 B1 B2 pA pB pp => wConst "congpi1"
  | sCongPi2 B1 B2 pA pB pp => wConst "congpi2"
  | sCongEq pA pu pv => wConst "congeq"
  | sCongRefl pA pu => wConst "congrefl"
  | sEqToHeq p => wConst "eqtoheq"
  | sHeqTypeEq A B p => wConst "heqtypeq"
  | sPack A1 A2 => wConst "pack" (* wPack (tsl A1) (tsl A2) *)
  | sProjT1 p => wConst "projT1" (* wProjT1 (tsl p) *)
  | sProjT2 p => wConst "projT2" (* wProjT2 (tsl p) *)
  | sProjTe p => wConst "projTe" (* wProjTe (tsl p) *)
  | sAx id => wConst id
  end.

Program Fixpoint tsl_glob (Σ : sglobal_context) : wglobal_context :=
  match Σ with
  | d :: Σ =>
    {| dname := d.(SCommon.dname) ; dtype := tsl d.(SCommon.dtype) ; dbody := _ |}
    :: tsl_glob Σ
  | nil => nil
  end.
Next Obligation.
Admitted.

Fixpoint tsl_ctx (Γ : scontext) : wcontext :=
  match Γ with
  | A :: Γ => tsl A :: tsl_ctx Γ
  | nil => nil
  end.

(*

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

(* Lemma tsl_lookup : *)
(*   forall {Σ id ty}, *)
(*     SCommon.lookup_glob Σ id = Some ty -> *)
(*     lookup_glob (tsl_glob Σ) id = Some (tsl ty). *)
(* Proof. *)
(*   intro Σ. induction Σ ; intros id ty eq. *)
(*   - cbn in eq. discriminate eq. *)
(*   - revert eq. cbn. case_eq (ident_eq id (SCommon.dname a)). *)
(*     + intros e eq. inversion eq. subst. reflexivity. *)
(*     + intros e eq. eapply IHΣ. assumption. *)
(* Defined. *)

(* Lemma nl_tsl : *)
(*   forall {u v}, *)
(*     Equality.nl u = Equality.nl v -> *)
(*     WEquality.nl (tsl u) = WEquality.nl (tsl v). *)
(* Proof. *)
(*   intro u. induction u ; intros v eq. *)
(*   all: destruct v ; simpl in eq ; try discriminate eq. *)
(*   all: try ( *)
(*     cbn ; inversion eq ; f_equal ; *)
(*     try eapply IHu ; *)
(*     try eapply IHu1 ; try eapply IHu2 ; *)
(*     try eapply IHu3 ; try eapply IHu4 ; *)
(*     try eapply IHu5 ; try eapply IHu6 ; *)
(*     assumption *)
(*   ). *)
(* Defined. *)

(* Open Scope i_scope. *)

(* Ltac lift_sort := *)
(*   match goal with *)
(*   | |- _ ;;; _ |-w lift ?n ?k ?t : ?S => change S with (lift n k S) *)
(*   | |- _ ;;; _ |-w ?t { ?n := ?u } : ?S => change S with (S {n := u}) *)
(*   end. *)

(* Ltac callih := *)
(*   match goal with *)
(*   | h : let _ := _ in *)
(*         let _ := tsl ?t in *)
(*         let _ := _ in _ -> _ ;;; _ |-w _ : _ *)
(*     |- _ ;;; _ |-w tsl ?t : _ => *)
(*     eapply h *)
(*   end. *)

(* Ltac wfctx := *)
(*   first [ *)
(*     eassumption *)
(*     | cbn ; eapply wf_snoc ; try assumption *)
(*   ]. *)

(* Ltac ih := *)
(*   repeat (callih ; wfctx). *)

(* Ltac go t' A' := *)
(*   unfold t', A' ; cbn ; *)
(*   repeat (rewrite ?tsl_lift, ?tsl_subst) ; *)
(*   econstructor ; try assumption ; ih. *)

(* Lemma tsl_sound : *)
(*   forall {Σ Γ t A}, *)
(*     let Σ' := tsl_glob Σ in *)
(*     let Γ' := tsl_ctx Γ in *)
(*     let t' := tsl t in *)
(*     let A' := tsl A in *)
(*     type_glob Σ' -> *)
(*     wf Σ' Γ' -> *)
(*     Σ ;;; Γ |-i t : A -> *)
(*     Σ' ;;; Γ' |-w t' : A'. *)
(* Proof. *)
(*   intros Σ Γ t A Σ' Γ' t' A' hg hw h. induction h. *)
(*   all: try solve [go t' A']. *)
(*   - unfold t', A'. cbn. rewrite tsl_lift. unshelve erewrite tsl_safe_nth. *)
(*     + cbn. rewrite tsl_ctx_length. assumption. *)
(*     + econstructor. assumption. *)
(*   - unfold t', A'. cbn. econstructor ; try assumption ; try ih. *)
(*     rewrite <- tsl_subst. ih. *)
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
(*       exists s. change (wSort s) with (tsl (sSort s)). *)
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
(*       change (wSort s) with (tsl (sSort s)) *)
(*     end. *)
(*     eapply tsl_sound ; try eassumption. *)
(*     eapply tsl_glob_sound. assumption. *)
(* Defined. *)

(* Corollary tsl_soundness : *)
(* forall {Σ Γ t A}, *)
(*     let Σ' := tsl_glob Σ in *)
(*     let Γ' := tsl_ctx Γ in *)
(*     let t' := tsl t in *)
(*     let A' := tsl A in *)
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

*)

End Translation.