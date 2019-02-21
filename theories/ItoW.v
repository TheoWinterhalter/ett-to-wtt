
From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Template
Require Import Ast utils monad_utils Typing Checker.
From Translation
     Require Import util Sorts SAst SLiftSubst WAst WLiftSubst
     SCommon ITyping
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
  | sPi2 A B p => wPi1 (tsl A) (tsl B) (tsl p)
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

Open Scope i_scope.

Lemma tsl_sound :
  forall {Σ Γ t A},
    Σ ;;; Γ |-i t : A ->
    tsl_glob Σ ;;; tsl_ctx Γ |-w tsl t : tsl A.
Proof.
  intros Σ Γ t A h. induction h.
  - cbn. rewrite tsl_lift. unshelve erewrite tsl_safe_nth.
    + cbn. rewrite tsl_ctx_length. assumption.
    + econstructor. (* We actually have to prove things mutually. *)
Abort.

End s.