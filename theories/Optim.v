(* Optimisation on syntax *)
From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon XTyping Conversion ITyping
               ITypingInversions ITypingLemmata ITypingAdmissible.

(* For optimisation, we remark that we can decide whenever an heterogenous
   equality is reflexivity.
 *)
Inductive isHeqRefl : sterm -> Type :=
| is_HeqRefl A u : isHeqRefl (sHeqRefl A u).

Definition decHeqRefl t : dec (isHeqRefl t).
  refine (
    match t with
    | sHeqRefl A u => inleft (is_HeqRefl A u)
    | _ => inright (fun e => _)
    end
  ). all: inversion e.
Defined.



Definition optHeqSym p :=
  match p with
  | sHeqRefl A u => sHeqRefl A u
  | _ => sHeqSym p
  end.

Lemma opt_HeqSym :
  forall {Σ Γ A a B b p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i optHeqSym p : sHeq B b A a.
Proof.
  intros Σ Γ A a B b p hg h.
  case (decHeqRefl p).
  - intros i. destruct i as [C c].
    simpl. 
    ttinv h. destruct (heq_conv_inv h2) as [[[eA eu] eA'] ev].
    destruct (istype_type hg h) as [z heq]. ttinv heq.
    eapply type_conv.
    + eapply type_HeqRefl' ; eassumption.
    + eapply type_Heq ; eassumption.
    + apply cong_Heq ; assumption.
  - intros e. destruct p.
    16: exfalso ; apply e ; constructor.
    all: simpl ; apply type_HeqSym' ; assumption.
Defined.

Definition optHeqTrans p q :=
  match p,q with
  | sHeqRefl A u,  sHeqRefl _ _ => sHeqRefl A u
  | sHeqRefl A u, _ => q
  | _, sHeqRefl A u => p
  | _,_ => sHeqTrans p q
  end.

Lemma opt_HeqTrans :
  forall {Σ Γ A a B b C c p q},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i optHeqTrans p q : sHeq A a C c.
Proof.
  intros Σ Γ A a B b C c p q hg hp hq.
  assert (hT : isType Σ Γ (sHeq A a C c)).
  { eapply istype_type ; try assumption.
    eapply type_HeqTrans' ; eassumption.
  }
  destruct hT.
  case (decHeqRefl p) ; case (decHeqRefl q).
  - intros iq ip. destruct ip as [D d], iq as [E e].
    simpl.
    ttinv hp. destruct (heq_conv_inv h1) as [[[DA da] DB] db].
    ttinv hq. destruct (heq_conv_inv h4) as [[[EB eb] EC] ec].
    eapply type_conv.
    + eapply type_HeqRefl' ; eassumption.
    + eassumption.
    + conv rewrite <- EC, ec.
      conv rewrite EB, eb.
      conv rewrite <- DA, da.
      apply cong_Heq ; try apply conv_refl ; assumption.
  - intros bot ip. destruct ip as [D d].
    replace (optHeqTrans (sHeqRefl D d) q) with q.
    + ttinv hp. destruct (heq_conv_inv h1) as [[[DA da] DB] db].
      eapply type_conv ; try eassumption.
      conv rewrite <- DA, da. apply conv_sym.
      apply cong_Heq ; try apply conv_refl ; assumption.
    + destruct q. all: try reflexivity.
      exfalso. apply bot. constructor.
  - intros iq bot. destruct iq as [E e].
    replace (optHeqTrans p (sHeqRefl E e)) with p.
    + ttinv hq. destruct (heq_conv_inv h1) as [[[EB eb] EC] ec].
      eapply type_conv ; try eassumption.
      conv rewrite <- EB, eb.
      apply cong_Heq ; try apply conv_refl ; assumption.
    + destruct p. all: reflexivity.
  - intros bq bp.
    destruct p ; try (exfalso ; apply bp ; constructor).
    all: destruct q ; try (exfalso ; apply bq ; constructor).
    all: try (simpl ; eapply type_HeqTrans' ; eassumption).
Defined.