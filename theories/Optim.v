(* Optimisation on syntax *)
From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From Equations Require Import Equations.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon XTyping
ITyping ITypingInversions ITypingLemmata ITypingAdmissible.

Section Optim.

Context `{Sort_notion : Sorts.notion}.

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
    ttinv h.
    eapply meta_conv.
    + eapply type_HeqRefl' ; eassumption.
    + cbn in h3. inversion h3.
      cbn. f_equal ; eauto.
  - intros e. destruct p.
    17: exfalso ; apply e ; constructor.
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
    ttinv hp. cbn in h2. inversion h2.
    ttinv hq. cbn in h5. inversion h5. subst.
    eapply type_HeqRefl'. all: assumption.
  - intros bot ip. destruct ip as [D d].
    replace (optHeqTrans (sHeqRefl D d) q) with q.
    + ttinv hp. cbn in h2. inversion h2. subst.
      assumption.
    + destruct q. all: try reflexivity.
      exfalso. apply bot. constructor.
  - intros iq bot. destruct iq as [E e].
    replace (optHeqTrans p (sHeqRefl E e)) with p.
    + ttinv hq. cbn in h2. inversion h2. subst.
      assumption.
    + destruct p. all: reflexivity.
  - intros bq bp.
    destruct p ; try (exfalso ; apply bp ; constructor).
    all: destruct q ; try (exfalso ; apply bq ; constructor).
    all: try (simpl ; eapply type_HeqTrans' ; eassumption).
Defined.

Definition optTransport A B p t :=
  if Equality.eq_term A B then t else sTransport A B p t.

Lemma opt_Transport :
  forall {Σ Γ s A B p t},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i optTransport A B p t : B.
Proof.
  intros Σ Γ s A B p t hg hp ht.
  unfold optTransport.
  case_eq (Equality.eq_term A B).
  - intro h.
    destruct (istype_type hg hp) as [z hT].
    ttinv hT.
    eapply eq_term_spec in h. subst. assumption.
  - intros _. eapply type_Transport' ; eassumption.
Defined.

Definition optHeqToEq p :=
  match p with
  | sHeqRefl A a => sRefl A a
  | sEqToHeq e => e
  | _ => sHeqToEq p
  end.

Lemma opt_HeqToEq :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i optHeqToEq p : sEq A u v.
Proof.
  intros Σ Γ A u v p hg h.
  assert (hT : isType Σ Γ (sEq A u v)).
  { eapply istype_type ; try assumption.
    eapply type_HeqToEq' ; eassumption.
  }
  destruct hT.
  destruct p.
  all: try (simpl ; eapply type_HeqToEq' ; eassumption).
  - simpl. rename p1 into B, p2 into b.
    ttinv h. cbn in h3. inversion h3. subst.
    eapply type_Refl' ; eassumption.
  - simpl. ttinv h. rename A0 into B, u0 into a, v0 into b.
    inversion h5. subst. assumption.
Defined.

Fact opt_sort_heq :
  forall {Σ Γ s1 s2 A B e},
    type_glob Σ ->
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i optHeqToEq e : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s1 s2 A B e hg h.
  destruct (istype_type hg h) as [? hty].
  ttinv hty.
  eapply opt_HeqToEq ; try assumption.
  eapply heq_sort ; eassumption.
Defined.

Corollary opt_sort_heq_ex :
  forall {Σ Γ s1 s2 A B e},
    type_glob Σ ->
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    ∑ p, Σ ;;; Γ |-i p : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s A B e hg h.
  eexists. now eapply opt_sort_heq.
Defined.

Definition optHeqTransport p t :=
  (* match p with *)
  (* | sRefl s A => sHeqRefl A t *)
  (* | _ =>  *)
  (* end. *)
  sHeqTransport p t.

Lemma opt_HeqTransport :
  forall {Σ Γ s A B p t},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i optHeqTransport p t : sHeq A t B (sTransport A B p t).
Proof.
  intros Σ Γ s A B p t hg ht hp.
  simpl ; eapply type_HeqTransport' ; eassumption.
Defined.

Definition optEqToHeq p :=
  match p with
  | sRefl A x => sHeqRefl A x
  | _ => sEqToHeq p
  end.

Lemma opt_EqToHeq :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i optEqToHeq p : sHeq A u A v.
Proof.
  intros Σ Γ A u v p hg h.
  destruct p.
  all: try (simpl ; eapply type_EqToHeq' ; eassumption).
  simpl.
  ttinv h. cbn in h3. inversion h3. subst.
  eapply type_HeqRefl' ; eassumption.
Defined.

(* Tests if t does not depend on variable i *)
Fixpoint notdepi (t : sterm) (i : nat) {struct t} : bool :=
  match t with
  | sRel j => negb (i =? j)
  | sSort _ => true
  | sProd A B => notdepi A i && notdepi B (S i)
  | sLambda A B t => notdepi A i && notdepi B (S i) && notdepi t (S i)
  | sApp u A B v => notdepi A i && notdepi B (S i) && notdepi u i && notdepi v i
  | sSum A B => notdepi A i && notdepi B (S i)
  | sPair A B u v => notdepi A i && notdepi B (S i) && notdepi u i && notdepi v i
  | sPi1 A B p => notdepi A i && notdepi B (S i) && notdepi p i
  | sPi2 A B p => notdepi A i && notdepi B (S i) && notdepi p i
  | sEq A u v => notdepi A i && notdepi u i && notdepi v i
  | sRefl A u => notdepi A i && notdepi u i
  (* | sJ *)
  | sTransport A B p t =>
    notdepi A i && notdepi B i && notdepi p i && notdepi t i
  | sBeta t u =>
    notdepi t (S i) && notdepi u i
  | sHeq A a B b => notdepi A i && notdepi a i && notdepi B i && notdepi b i
  | sHeqToEq p => notdepi p i
  | sHeqRefl A u => notdepi A i && notdepi u i
  | sHeqSym p => notdepi p i
  | sHeqTrans p q => notdepi p i && notdepi q i
  | sHeqTransport p t => notdepi p i && notdepi t i
  | sCongProd B1 B2 pA pB =>
    notdepi B1 (S i) && notdepi B2 (S i) && notdepi pA i && notdepi pB (S i)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    notdepi B1 (S i) && notdepi B2 (S i) &&
    notdepi t1 (S i) && notdepi t2 (S i) &&
    notdepi pA i && notdepi pB (S i) && notdepi pt (S i)
  | sCongApp B1 B2 pu pA pB pv =>
    notdepi B1 (S i) && notdepi B2 (S i) &&
    notdepi pA i && notdepi pB (S i) &&
    notdepi pu i && notdepi pv i
  | sCongSum B1 B2 pA pB =>
    notdepi B1 (S i) && notdepi B2 (S i) && notdepi pA i && notdepi pB (S i)
  (* | sCongPair TODO *)
  (* | sCongPi1 TODO *)
  (* | sCongPi2 TODO *)
  | sCongEq pA pu pv => notdepi pA i && notdepi pu i && notdepi pv i
  | sCongRefl pA pu => notdepi pA i && notdepi pu i
  | sEqToHeq p => notdepi p i
  | sHeqTypeEq A B p => notdepi A i && notdepi B i && notdepi p i
  | sPack A B => notdepi A i && notdepi B i
  | sProjT1 p => notdepi p i
  | sProjT2 p => notdepi p i
  | sProjTe p => notdepi p i
  | sAx _ => true
  | _ => false
  end.

Definition notdep t := notdepi t 0.

Lemma notdepi_lift :
  forall {t i},
    notdepi t i = true ->
    lift 1 (S i) t = lift 1 i t.
Proof.
  intro t. induction t ; intros i h.
  all: try (cbn in h ; discriminate h).
  all: try (cbn in h ; repeat destruct_andb ;
            cbn ; f_equal ;
            rewrite_assumption ; (reflexivity || assumption)).
  revert h. cbn - [Nat.leb].
  ncase (i =? n).
  intros _. nat_case.
  - nat_case. reflexivity.
  - nat_case. reflexivity.
Defined.

Corollary notdep_lift :
  forall {t},
    notdep t = true ->
    lift 1 1 t = lift0 1 t.
Proof.
  intros t h.
  apply notdepi_lift. assumption.
Defined.

Definition optCongProd B1 B2 pA pB :=
  match pA, pB with
  | sHeqRefl (sSort s) A, sHeqRefl (sSort z) B =>
    if notdep B1 && notdep B2 then
      sHeqRefl (sSort (prod_sort s z)) (sProd A B1)
    else sCongProd B1 B2 pA pB
  | _,_ => sCongProd B1 B2 pA pB
  end.

Lemma opt_CongProd :
  forall {Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ;;; Γ,, sPack A1 A2 |-i
    pB : sHeq (sSort z1)
              ((lift 1 1 B1) {0 := sProjT1 (sRel 0)})
              (sSort z2)
              ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ->
    Σ;;; Γ,, A1 |-i B1 : sSort z1 ->
    Σ;;; Γ,, A2 |-i B2 : sSort z2 ->
    Σ;;; Γ |-i optCongProd B1 B2 pA pB
    : sHeq (sSort (prod_sort s1 z1)) (sProd A1 B1)
           (sSort (prod_sort s2 z2)) (sProd A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct pA.
  all: try (simpl ; eapply type_CongProd' ; eassumption).
  destruct pA1.
  all: try (simpl ; eapply type_CongProd' ; eassumption).
  destruct pB.
  all: try (simpl ; eapply type_CongProd' ; eassumption).
  destruct pB1.
  all: try (simpl ; eapply type_CongProd' ; eassumption).
  simpl.
  case_eq (notdep B1) ; try (intro ; simpl ; eapply type_CongProd' ; eassumption).
  case_eq (notdep B2) ; try (intros ; simpl ; eapply type_CongProd' ; eassumption).
  intros nd2 nd1. simpl.
  ttinv hpA. ttinv hpB.
  destruct (istype_type hg hpA) as [? hTA]. ttinv hTA.
  destruct (istype_type hg hpB) as [? hTB]. ttinv hTB.
  cbn in h2. inversion h2. subst.
  cbn in h5. inversion h5. subst.
  cbn in h15. inversion h15. subst. clear h15.
  cbn in h10. inversion h10. subst. clear h10.
  rewrite notdep_lift, lift_subst in H3 by assumption.
  rewrite notdep_lift, lift_subst in H3 by assumption. subst.
  eapply type_HeqRefl' ; try eassumption.
  eapply type_Prod ; eassumption.
Defined.

Definition optCongLambda B1 B2 t1 t2 pA pB pt :=
  match pA, pB, pt with
  | sHeqRefl _ A, sHeqRefl _ _, sHeqRefl _ _ =>
    if notdep B1 && notdep B2 && notdep t1 && notdep t2 then
      sHeqRefl (sProd A B1) (sLambda A B1 t1)
    else sCongLambda B1 B2 t1 t2 pA pB pt
  | _,_,_ => sCongLambda B1 B2 t1 t2 pA pB pt
  end.

Lemma opt_CongLambda :
  forall {Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ;;; Γ,, sPack A1 A2 |-i pB
    : sHeq (sSort z1) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)})
           (sSort z2) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ->
    Σ;;; Γ,, sPack A1 A2 |-i pt
    : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)})
           ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
           ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})
           ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}) ->
    Σ;;; Γ,, A1 |-i B1 : sSort z1 ->
    Σ;;; Γ,, A2 |-i B2 : sSort z2 ->
    Σ;;; Γ,, A1 |-i t1 : B1 ->
    Σ;;; Γ,, A2 |-i t2 : B2 ->
    Σ;;; Γ |-i optCongLambda B1 B2 t1 t2 pA pB pt
    : sHeq (sProd A1 B1) (sLambda A1 B1 t1)
           (sProd A2 B2) (sLambda A2 B2 t2).
Proof.
  intros Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 t1 t2 pA pB pt
         hg hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct pA.
  all: try (simpl ; eapply type_CongLambda' ; eassumption).
  destruct pB.
  all: try (simpl ; eapply type_CongLambda' ; eassumption).
  destruct pt.
  all: try (simpl ; eapply type_CongLambda' ; eassumption).
  simpl.
  case_eq (notdep B1) ; try (intro ; simpl ; eapply type_CongLambda' ; eassumption).
  case_eq (notdep B2) ; try (intros ; simpl ; eapply type_CongLambda' ; eassumption).
  case_eq (notdep t1) ; try (intros ; simpl ; eapply type_CongLambda' ; eassumption).
  case_eq (notdep t2) ; try (intros ; simpl ; eapply type_CongLambda' ; eassumption).
  intros ndt2 ndt1 ndB2 ndB1. simpl.
  ttinv hpA. ttinv hpB. ttinv hpt.
  destruct (istype_type hg hpA) as [? hTA]. ttinv hTA.
  destruct (istype_type hg hpB) as [? hTB]. ttinv hTB.
  destruct (istype_type hg hpt) as [? hTt]. ttinv hTt.
  cbn in h2. inversion h2.
  cbn in h5. inversion h5.
  cbn in h8. inversion h8. subst.
  rewrite notdep_lift, lift_subst in H7 by assumption.
  rewrite notdep_lift, lift_subst in H7 by assumption.
  subst.
  rewrite notdep_lift, lift_subst in H11 by assumption.
  rewrite notdep_lift, lift_subst in H11 by assumption.
  subst.
  eapply type_HeqRefl' ; try eassumption.
  eapply type_Lambda ; eassumption.
Defined.

Definition optCongApp B1 B2 pu pA pB pv :=
  match pA, pB, pu, pv with
  | sHeqRefl _ A, sHeqRefl _ _, sHeqRefl _ u, sHeqRefl _ v =>
    if notdep B1 && notdep B2 then
      sHeqRefl (B1{ 0 := v }) (sApp u A B1 v)
    else sCongApp B1 B2 pu pA pB pv
  | _,_,_,_ => sCongApp B1 B2 pu pA pB pv
  end.

Lemma opt_CongApp :
  forall {Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ;;; Γ,, sPack A1 A2 |-i pB
    : sHeq (sSort z1) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)})
           (sSort z2) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ->
    Σ;;; Γ |-i pu : sHeq (sProd A1 B1) u1 (sProd A2 B2) u2 ->
    Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ;;; Γ,, A1 |-i B1 : sSort z1 ->
    Σ;;; Γ,, A2 |-i B2 : sSort z2 ->
    Σ;;; Γ |-i optCongApp B1 B2 pu pA pB pv
    : sHeq (B1 {0 := v1}) (sApp u1 A1 B1 v1) (B2 {0 := v2}) (sApp u2 A2 B2 v2).
Proof.
  intros Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct pA.
  all: try (simpl ; eapply type_CongApp' ; eassumption).
  destruct pB.
  all: try (simpl ; eapply type_CongApp' ; eassumption).
  destruct pu.
  all: try (simpl ; eapply type_CongApp' ; eassumption).
  destruct pv.
  all: try (simpl ; eapply type_CongApp' ; eassumption).
  simpl.
  case_eq (notdep B1) ; try (intro ; simpl ; eapply type_CongApp' ; eassumption).
  case_eq (notdep B2) ; try (intros ; simpl ; eapply type_CongApp' ; eassumption).
  intros ndB2 ndB1. simpl.
  ttinv hpA. ttinv hpB. ttinv hpu. ttinv hpv.
  destruct (istype_type hg hpA) as [? hTA]. ttinv hTA.
  destruct (istype_type hg hpB) as [? hTB]. ttinv hTB.
  destruct (istype_type hg hpu) as [? hTu]. ttinv hTu.
  destruct (istype_type hg hpv) as [? hTv]. ttinv hTv.
  cbn in h2. inversion h2.
  cbn in h5. inversion h5.
  cbn in h8. inversion h8.
  cbn in h11. inversion h11. subst.
  inversion H10. subst.
  eapply type_HeqRefl' ; try eassumption.
  eapply type_App ; eassumption.
Defined.

(* TODO congSum, congPair, congPi1, congPi2 *)

Definition optCongEq pA pu pv :=
  match pA, pu, pv with
  | sHeqRefl (sSort s) A, sHeqRefl _ u, sHeqRefl _ v =>
    sHeqRefl (sSort (eq_sort s)) (sEq A u v)
  | _,_,_ => sCongEq pA pu pv
  end.

Lemma opt_CongEq :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv},
    type_glob Σ ->
    Σ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ;;; Γ |-i optCongEq pA pu pv :
              sHeq (sSort (eq_sort s1)) (sEq A1 u1 v1)
                   (sSort (eq_sort s2)) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv hg hpA hpu hpv.
  destruct pA.
  all: try (simpl ; eapply type_CongEq' ; eassumption).
  destruct pA1.
  all: try (simpl ; eapply type_CongEq' ; eassumption).
  destruct pu.
  all: try (simpl ; eapply type_CongEq' ; eassumption).
  destruct pv.
  all: try (simpl ; eapply type_CongEq' ; eassumption).
  simpl.
  ttinv hpA. ttinv hpu. ttinv hpv.
  destruct (istype_type hg hpA) as [? hTA]. ttinv hTA.
  destruct (istype_type hg hpu) as [? hTu]. ttinv hTu.
  destruct (istype_type hg hpv) as [? hTv]. ttinv hTv.
  cbn in h2. inversion h2.
  cbn in h5. inversion h5.
  cbn in h8. inversion h8. subst.
  eapply type_HeqRefl' ; try eassumption.
  eapply type_Eq ; eassumption.
Defined.

Definition optCongRefl pA pu :=
  match pA, pu with
  | sHeqRefl _ A, sHeqRefl _ u =>
    sHeqRefl (sEq A u u) (sRefl A u)
  | _,_ => sCongRefl pA pu
  end.

Lemma opt_CongRefl :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 pA pu},
    type_glob Σ ->
    Σ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ;;; Γ |-i optCongRefl pA pu : sHeq (sEq A1 u1 u1) (sRefl A1 u1)
                                       (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 pA pu hg hpA hpu.
  destruct pA.
  all: try (simpl ; eapply type_CongRefl' ; eassumption).
  destruct pu.
  all: try (simpl ; eapply type_CongRefl' ; eassumption).
  simpl.
  ttinv hpA. ttinv hpu.
  destruct (istype_type hg hpA) as [? hTA]. ttinv hTA.
  destruct (istype_type hg hpu) as [? hTu]. ttinv hTu.
  cbn in h2. inversion h2.
  cbn in h5. inversion h5. subst.
  eapply type_HeqRefl' ; try eassumption.
  eapply type_Refl' ; eassumption.
Defined.

End Optim.
