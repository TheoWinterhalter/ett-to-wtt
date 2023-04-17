From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon XTyping ITyping
               ITypingInversions ITypingLemmata ITypingAdmissible Optim
               Uniqueness PackLifts.
Import ListNotations.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.

(*! Relation for translated expressions *)

Section Sim.

Context `{Sort_notion : Sorts.notion}.

Reserved Notation " t1 ∼ t2 " (at level 20).

Inductive trel : sterm -> sterm -> Type :=
| trel_Rel x :
    sRel x ∼ sRel x

| trel_Transport_l t1 t2 T1 T2 p :
    t1 ∼ t2 ->
    sTransport T1 T2 p t1 ∼ t2

| trel_Transport_r t1 t2 T1 T2 p :
    t1 ∼ t2 ->
    t1 ∼ sTransport T1 T2 p t2

| trel_Prod n1 n2 A1 A2 B1 B2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    sProd n1 A1 B1 ∼ sProd n2 A2 B2

| trel_Sum n1 n2 A1 A2 B1 B2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    sSum n1 A1 B1 ∼ sSum n2 A2 B2

| trel_Eq A1 A2 u1 u2 v1 v2 :
    A1 ∼ A2 ->
    u1 ∼ u2 ->
    v1 ∼ v2 ->
    sEq A1 u1 v1 ∼ sEq A2 u2 v2

| trel_Sort s :
    sSort s ∼ sSort s

| trel_Lambda n1 n2 A1 A2 B1 B2 u1 u2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    u1 ∼ u2 ->
    sLambda n1 A1 B1 u1 ∼ sLambda n2 A2 B2 u2

| trel_App u1 u2 A1 A2 B1 B2 v1 v2 :
    u1 ∼ u2 ->
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    v1 ∼ v2 ->
    sApp u1 A1 B1 v1 ∼ sApp u2 A2 B2 v2

| trel_Pair A1 A2 B1 B2 u1 u2 v1 v2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    u1 ∼ u2 ->
    v1 ∼ v2 ->
    sPair A1 B1 u1 v1 ∼ sPair A2 B2 u2 v2

| trel_Pi1 A1 A2 B1 B2 p1 p2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    p1 ∼ p2 ->
    sPi1 A1 B1 p1 ∼ sPi1 A2 B2 p2

| trel_Pi2 A1 A2 B1 B2 p1 p2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    p1 ∼ p2 ->
    sPi2 A1 B1 p1 ∼ sPi2 A2 B2 p2

| trel_Refl A1 A2 u1 u2 :
    A1 ∼ A2 ->
    u1 ∼ u2 ->
    sRefl A1 u1 ∼ sRefl A2 u2

| trel_Ax id :
    sAx id ∼ sAx id

where " t1 ∼ t2 " := (trel t1 t2).

End Sim.

Notation " t1 ∼ t2 " := (trel t1 t2) (at level 20).
Derive Signature for trel.

Section In.

Context `{Sort_notion : Sorts.notion}.

(* We also define a biased relation that only allows transports on one side,
   the idea being that the term on the other side belongs to the source.
   This might be unnecessary as transport isn't typable in the source but
   hopefully this is more straightforward.
 *)
Reserved Notation " t ⊏ t' " (at level 20).

(* The first is in the source, the second in the target. *)
Inductive inrel : sterm -> sterm -> Type :=
| inrel_Rel x :
    sRel x ⊏ sRel x

| inrel_Transport t t' T1 T2 p :
    t ⊏ t' ->
    t ⊏ sTransport T1 T2 p t'

| inrel_Prod n n' A A' B B' :
    A ⊏ A' ->
    B ⊏ B' ->
    sProd n A B ⊏ sProd n' A' B'

| inrel_Sum n n' A A' B B' :
    A ⊏ A' ->
    B ⊏ B' ->
    sSum n A B ⊏ sSum n' A' B'

| inrel_Eq A A' u u' v v' :
    A ⊏ A' ->
    u ⊏ u' ->
    v ⊏ v' ->
    sEq A u v ⊏ sEq A' u' v'

| inrel_Sort s :
    sSort s ⊏ sSort s

| inrel_Lambda n n' A A' B B' u u' :
    A ⊏ A' ->
    B ⊏ B' ->
    u ⊏ u' ->
    sLambda n A B u ⊏ sLambda n' A' B' u'

| inrel_App u u' A A' B B' v v' :
    u ⊏ u' ->
    A ⊏ A' ->
    B ⊏ B' ->
    v ⊏ v' ->
    sApp u A B v ⊏ sApp u' A' B' v'

| inrel_Pair A A' B B' u u' v  v' :
    A ⊏ A' ->
    B ⊏ B' ->
    u ⊏ u' ->
    v ⊏ v' ->
    sPair A B u v ⊏ sPair A' B' u' v'

| inrel_Pi1 A A' B B' p p' :
    A ⊏ A' ->
    B ⊏ B' ->
    p ⊏ p' ->
    sPi1 A B p ⊏ sPi1 A' B' p'

| inrel_Pi2 A A' B B' p p' :
    A ⊏ A' ->
    B ⊏ B' ->
    p ⊏ p' ->
    sPi2 A B p ⊏ sPi2 A' B' p'

| inrel_Refl A A' u u' :
    A ⊏ A' ->
    u ⊏ u' ->
    sRefl A u ⊏ sRefl A' u'

| inrel_Ax id :
    sAx id ⊏ sAx id

where " t ⊏ t' " := (inrel t t').

Lemma inrel_trel :
  forall {t t'}, t ⊏ t' -> t ∼ t'.
Proof.
  intros t t' h.
  induction h ; now constructor.
Defined.

Lemma inrel_optTransport :
  forall {A B p t t'},
    t ⊏ t' ->
    t ⊏ optTransport A B p t'.
Proof.
  intros A B p t t' h.
  unfold optTransport.
  destruct (Equality.eq_term A B).
  - assumption.
  - constructor. assumption.
Defined.

End In.

Notation " t ⊏ t' " := (inrel t t') (at level 20).

Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-i lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-i llift ?n ?k ?t : ?S => change S with (llift n k S)
  | |- _ ;;; _ |-i rlift ?n ?k ?t : ?S => change S with (rlift n k S)
  | |- _ ;;; _ |-i ?t { ?n := ?u } : ?S => change S with (S {n := u})
  | |- sSort ?s = lift ?n ?k ?t =>
    change (sSort s) with (lift n k (sSort s))
  | |- sSort ?s = llift ?n ?k ?t =>
    change (sSort s) with (llift n k (sSort s))
  | |- sSort ?s = rlift ?n ?k ?t =>
    change (sSort s) with (rlift n k (sSort s))
  | |- sSort ?s = ?t{ ?n := ?u } =>
    change (sSort s) with ((sSort s){ n := u })
  | |- lift ?n ?k ?t = sSort ?s =>
    change (sSort s) with (lift n k (sSort s))
  | |- llift ?n ?k ?t = sSort ?s =>
    change (sSort s) with (llift n k (sSort s))
  | |- rlift ?n ?k ?t = sSort ?s =>
    change (sSort s) with (rlift n k (sSort s))
  | |- ?t{ ?n := ?u } = sSort ?s =>
    change (sSort s) with ((sSort s){ n := u })
  end.

Section Fundamental.

Context `{Sort_notion : Sorts.notion}.

Ltac cleannl :=
  let inv h :=
    inversion h ; subst ; clear h
  in
  let aux t h :=
    destruct t ; cbn in h ; try discriminate h ; inv h
  in
  repeat match goal with
  | h : context [ nl (sSort _) ] |- _ => cbn in h
  | h : context [ nl (sProd _ _ _) ] |- _ => cbn in h
  | h : context [ nl (sSum _ _ _) ] |- _ => cbn in h
  | h : nlSort _ = nlSort _ |- _ => inv h
  | h : nlProd _ _ = nlProd _ _ |- _ => inv h
  | h : nlSum _ _ = nlSum _ _ |- _ => inv h
  | h : nl ?t = nlSort _ |- _ => aux t h
  | h : nlSort _ = nl ?t |- _ => aux t h
  | h : nlProd _ _ = nl ?t |- _ => aux t h
  | h : nl ?t = nlProd _ _ |- _ => aux t h
  | h : nlSum _ _ = nl ?t |- _ => aux t h
  | h : nl ?t = nlSum _ _ |- _ => aux t h
  end.

Lemma trel_to_heq' :
  forall {Σ t1 t2},
    type_glob Σ ->
    t1 ∼ t2 ->
    forall Γ Γ1 Γ2,
      ∑ p,
        forall Γm T1 T2,
          ismix Σ Γ Γ1 Γ2 Γm ->
          Σ ;;; Γ ,,, Γ1 |-i t1 : T1 ->
          Σ ;;; Γ ,,, Γ2 |-i t2 : T2 ->
          Σ ;;; Γ ,,, Γm |-i p : sHeq (llift0 #|Γm| T1)
                                     (llift0 #|Γm| t1)
                                     (rlift0 #|Γm| T2)
                                     (rlift0 #|Γm| t2).
Proof.
  intros Σ t1 t2 hg sim.
  induction sim ; intros Γ Γ1 Γ2.

  (* Variable *)
  - case_eq (x <? #|Γ1|) ; intro e0 ; bprop e0.
    + (* The variable is located in the mixed part.
         We use the available equality.
       *)
      exists (sProjTe (sRel x)).
      intros Γm U1 U2 hm h1 h2.
      unfold llift at 2. unfold rlift at 2.
      case_eq (x <? 0) ; intro e ; bprop e ; try mylia. clear e2.
      pose proof (mix_length1 hm) as ml. rewrite <- ml in e0, e1.
      change (0 + #|Γm|)%nat with #|Γm|.
      rewrite e0.
      (* Now for the specifics *)
      apply type_ProjTe' ; try assumption.
      ttinv h1. ttinv h2.
      rename H into en1, H1 into en2, H0 into hx1, H2 into hx2.
      assert (is1' : x < #|Γ1|) by (erewrite mix_length1 in e1 ; eassumption).
      assert (is2' : x < #|Γ2|) by (erewrite mix_length2 in e1 ; eassumption).
      destruct (istype_type hg h1) as [s1 ?].
      destruct (istype_type hg h2) as [s2 ?].
      unfold ",,," in en1. rewrite nth_error_app1 in en1 by auto.
      unfold ",,," in en2. rewrite nth_error_app1 in en2 by auto.
      eapply ismix_nth_sort in hm as hm'. 2-4: eassumption.
      destruct hm' as [ss [? ?]].
      eapply type_rename.
      * eapply type_Rel.
        -- eapply (@wf_llift Sort_notion) with (Δ := []) ; try eassumption.
           eapply typing_wf ; eassumption.
        -- unfold ",,,". rewrite nth_error_app1 by auto.
           eapply nth_error_mix. all: eassumption.
      * cbn. f_equal.
        -- rewrite lift_llift.
           replace (S x + (#|Γm| - S x))%nat with #|Γm| by mylia.
           eapply nl_llift. eassumption.
        -- rewrite lift_rlift.
           replace (S x + (#|Γm| - S x))%nat with #|Γm| by mylia.
           eapply nl_rlift. eassumption.
    + (* Unless it is ill-typed, the variable is in Γ, reflexivity will do.
         To type reflexivity properly we still need a proof that
         x - #|Γ1| < #|Γ|. We have to consider both cases.
       *)
      case_eq ((x - #|Γ1|) <? #|Γ|) ; intro isdecl ; bprop isdecl.
      * (* The variable is indeed in the context. *)
        set (y := x - #|Γ1|) in *.
        case_eq (nth_error Γ y).
        2:{ intros e. apply nth_error_None in e. mylia. }
        intros B en.
        set (A := lift0 (S x) B).
        exists (sHeqRefl A (sRel x)).
        intros Γm U1 U2 hm h1 h2.
        unfold llift at 2. unfold rlift at 2.
        case_eq (x <? 0) ; intro e ; bprop e ; try mylia. clear e2.
        pose proof (mix_length1 hm) as ml. rewrite <- ml in e0, e1.
        change (0 + #|Γm|)%nat with #|Γm|.
        rewrite e0.
        (* Now for the specifics *)
        assert (h1' : Σ ;;; Γ ,,, Γm |-i sRel x : llift0 #|Γm| U1).
        { replace (sRel x) with (llift0 #|Γm| (sRel x)).
          2:{
            unfold llift. rewrite e.
            change (0 + #|Γm|)%nat with #|Γm|. rewrite e0.
            reflexivity.
          }
          eapply type_llift0 ; eassumption.
        }
        assert (h2' : Σ ;;; Γ ,,, Γm |-i sRel x : rlift0 #|Γm| U2).
        { replace (sRel x) with (rlift0 #|Γm| (sRel x)).
          2:{
            unfold rlift. rewrite e.
            change (0 + #|Γm|)%nat with #|Γm|. rewrite e0.
            reflexivity.
          }
          eapply type_rlift0 ; eassumption.
        }
        pose proof (uniqueness hg h1' h2').
        destruct (istype_type hg h1').
        destruct (istype_type hg h2').
        eapply type_rename.
        -- eapply type_HeqRefl' ; try eassumption.
           subst y A.
           eapply type_Rel.
           ++ eapply typing_wf. eassumption.
           ++ unfold ",,,". rewrite nth_error_app2 by mylia.
              rewrite ml. assumption.
        -- cbn. ttinv h1'. ttinv h2'. f_equal.
           ++ subst y A. rewrite <- H3.
              unfold ",,," in H2. rewrite nth_error_app2 in H2 by mylia.
              rewrite ml in H2. rewrite en in H2. inversion H2. reflexivity.
           ++ subst y A. rewrite <- H5.
              unfold ",,," in H4. rewrite nth_error_app2 in H4 by mylia.
              rewrite ml in H4. rewrite en in H4. inversion H4. reflexivity.
      * (* In case the variable isn't in the context at all,
           it is bound to be ill-typed and we can return garbage.
         *)
        exists (sRel 0).
        intros Γm U1 U2 hm h1 h2.
        exfalso. ttinv h1. apply nth_error_Some_length in H.
        unfold ",,," in H. rewrite length_cat in H. mylia.
  (* Left transport *)
  - destruct (IHsim Γ Γ1 Γ2) as [q hq].
    exists (optHeqTrans (optHeqSym (optHeqTransport (llift0 #|Γ1| p) (llift0 #|Γ1| t1))) q).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1.
    specialize (hq _ _ _ hm h h2).
    destruct (istype_type hg hq) as [s' h'].
    ttinv h'. cbn in h11. inversion h11. subst. clear h11.
    eapply opt_HeqTrans ; try assumption.
    + eapply opt_HeqSym ; try assumption.
      eapply type_rename.
      * eapply opt_HeqTransport ; try assumption.
        -- eapply type_llift0 ; eassumption.
        -- instantiate (2 := s). instantiate (1 := llift0 #|Γm| U1).
           change (sEq (sSort s) (llift0 #|Γm| T1) (llift0 #|Γm| U1))
             with (llift0 #|Γm| (sEq (sSort s) T1 U1)).
           eapply type_llift0 ; try eassumption.
           eapply type_rename ; try eassumption.
           cbn. f_equal. eauto.
      * cbn. f_equal. f_equal. eapply nl_llift. eauto.
    + assumption.

  (* Right transport *)
  - destruct (IHsim Γ Γ1 Γ2) as [q hq].
    exists (optHeqTrans q (optHeqTransport (rlift0 #|Γ1| p) (rlift0 #|Γ1| t2))).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h2.
    specialize (hq _ _ _ hm h1 h).
    destruct (istype_type hg hq) as [s' h'].
    ttinv h'. cbn in h11. inversion h11. subst. clear h11.
    cbn.
    eapply opt_HeqTrans ; try assumption.
    + eassumption.
    + eapply type_rename.
      * eapply opt_HeqTransport ; try eassumption.
        instantiate (2 := s). instantiate (1 := rlift0 #|Γm| T2).
        change (sEq (sSort s) (rlift0 #|Γm| T1) (rlift0 #|Γm| T2))
          with (rlift0 #|Γm| (sEq (sSort s) T1 T2)).
        eapply type_rlift0 ; eassumption.
      * cbn. f_equal. eapply nl_rlift. eauto.

  (* Prod *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    exists (optCongProd (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pA pB).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h0 h5).
    destruct (istype_type hg hpA) as [s iA].
    ttinv iA. cbn in h12. inversion h12. subst. clear h12.
    cleannl.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h h3).
    destruct (istype_type hg hpB) as [? iB]. ttinv iB.
    cbn in h14. inversion h14. subst. clear h14.
    assert (s3 = s2).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    destruct (istype_type hg h1).
    destruct (istype_type hg h2).
    eapply type_rename.
    + eapply opt_CongProd ; try assumption.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * lift_sort.
        eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort.
        eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. reflexivity.

  (* Sum *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    exists (sCongSum (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pA pB).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h0 h5).
    destruct (istype_type hg hpA) as [s iA].
    ttinv iA. cbn in h12. inversion h12. subst. clear h12.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h h3).
    destruct (istype_type hg hpB) as [? iB]. ttinv iB.
    cbn in h16. inversion h16. subst. clear h16.
    cleannl.
    assert (s3 = s2).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    destruct (istype_type hg h1).
    destruct (istype_type hg h2).
    eapply type_rename.
    + eapply type_CongSum' ; try assumption.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * lift_sort.
        eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort.
        eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. reflexivity.

  (* Eq *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ Γ1 Γ2) as [pu hpu].
    destruct (IHsim3 Γ Γ1 Γ2) as [pv hpv].
    exists (optCongEq pA pu pv).
    intros Γm U1 U2 hm h1 h2.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h0 h6).
    specialize (hpu _ _ _ hm h h4).
    specialize (hpv _ _ _ hm h3 h7).
    destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
    cbn in h14. inversion h14. subst. clear h14.
    cleannl.
    assert (s0 = s).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    eapply type_rename.
    + eapply opt_CongEq ; eassumption.
    + cbn. reflexivity.

  (* Sort *)
  - exists (sHeqRefl (sSort (Sorts.succ s)) (sSort s)).
    intros Γm U1 U2 hm h1 h2.
    ttinv h1. ttinv h2.
    cleannl.
    assert (hwf : wf Σ (Γ ,,, Γm)).
    { eapply (@wf_llift Sort_notion) with (Δ := []) ; try eassumption.
      eapply typing_wf ; eassumption.
    }
    eapply type_rename.
    + eapply type_HeqRefl' ; try assumption.
      apply type_Sort. eassumption.
    + reflexivity.

  (* Lambda *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    destruct (IHsim3 Γ (Γ1,, A1) (Γ2,, A2)) as [pu hpu].
    exists (optCongLambda (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2)
                   (llift #|Γ1| 1 u1) (rlift #|Γ1| 1 u2) pA pB pu).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h0 h6).
    destruct (istype_type hg hpA) as [? iA]. ttinv iA.
    cleannl.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h h4).
    specialize (hpu _ _ _ hm' h3 h7).
    assert (s3 = s2).
    { destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
      cleannl. eapply sorts_in_sort ; eassumption.
    } subst.
    eapply type_rename.
    + eapply opt_CongLambda ; try assumption.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj. apply hpB.
      * rewrite !llift_substProj, !rlift_substProj. apply hpu.
      * lift_sort.
        eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort.
        eapply (@type_rlift1 Sort_notion) ; eassumption.
      * eapply (@type_llift1 Sort_notion) ; eassumption.
      * eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. f_equal. all: f_equal.
      all: try eapply nl_llift.
      all: try eapply nl_rlift.
      all: eauto.

  (* App *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pu hpu].
    destruct (IHsim2 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim3 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    destruct (IHsim4 Γ Γ1 Γ2) as [pv hpv].
    exists (optCongApp (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pu pA pB pv).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpu _ _ _ hm h3 h8).
    specialize (hpA _ _ _ hm h0 h7).
    destruct (istype_type hg hpA) as [? iA].
    ttinv iA. cleannl.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h h5).
    specialize (hpv _ _ _ hm h4 h9).
    assert (s3 = s2).
    { destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
      cleannl. eapply sorts_in_sort ; eassumption.
    } subst.
    eapply type_rename.
    + eapply opt_CongApp ; try assumption.
      * apply hpA.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * apply hpu.
      * apply hpv.
      * lift_sort.
        eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort.
        eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. rewrite <- llift_subst, <- rlift_subst. f_equal.
      * cbn. eapply nl_llift. assumption.
      * cbn. eapply nl_rlift. assumption.

  (* Pair *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    destruct (IHsim3 Γ Γ1 Γ2) as [pu hpu].
    destruct (IHsim4 Γ Γ1 Γ2) as [pv hpv].
    clear IHsim1 IHsim2 IHsim3 IHsim4.
    exists (sCongPair (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pA pB pu pv).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h0 h7).
    destruct (istype_type hg hpA) as [? iA].
    ttinv iA. cleannl.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h h5).
    assert (s3 = s2).
    { destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
      cleannl. eapply sorts_in_sort ; eassumption.
    } subst.
    specialize (hpu _ _ _ hm h3 h8).
    specialize (hpv _ _ _ hm h4 h9).
    eapply type_rename.
    + eapply type_CongPair' ; try assumption.
      * apply hpA.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * apply hpu.
      * replace 0 with (0 + 0)%nat in hpv by mylia.
        rewrite llift_subst, rlift_subst in hpv.
        apply hpv.
      * lift_sort. eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort. eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. f_equal. all: f_equal.
      all: try eapply nl_llift.
      all: try eapply nl_rlift.
      all: eauto.

  (* Pi1 *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    destruct (IHsim3 Γ Γ1 Γ2) as [pp hpp].
    exists (sCongPi1 (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pA pB pp).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h h4).
    destruct (istype_type hg hpA) as [? iA].
    ttinv iA. cleannl.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h3 h7).
    assert (s3 = s2).
    { destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
      cleannl. eapply sorts_in_sort ; eassumption.
    } subst.
    specialize (hpp _ _ _ hm h0 h6).
    eapply type_rename.
    + eapply type_CongPi1' ; try assumption.
      * apply hpA.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * apply hpp.
      * lift_sort. eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort. eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. f_equal.
      all: try eapply nl_llift.
      all: try eapply nl_rlift.
      all: eauto.

  (* Pi2 *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ (Γ1,, A1) (Γ2,, A2)) as [pB hpB].
    destruct (IHsim3 Γ Γ1 Γ2) as [pp hpp].
    exists (sCongPi2 (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pA pB pp).
    intros Γm U1 U2 hm h1 h2.
    pose proof (mix_length1 hm) as ml. rewrite <- ml.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h h4).
    destruct (istype_type hg hpA) as [? iA].
    ttinv iA. cleannl.
    assert (s1 = s0).
    { eapply sorts_in_sort ; eassumption. }
    subst.
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, A1)
                    (Γ2 ,, A2)
                    (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor ; eassumption. }
    specialize (hpB _ _ _ hm' h3 h7).
    assert (s3 = s2).
    { destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
      cleannl. eapply sorts_in_sort ; eassumption.
    } subst.
    specialize (hpp _ _ _ hm h0 h6).
    eapply type_rename.
    + eapply type_CongPi2' ; try assumption.
      * apply hpA.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * apply hpp.
      * lift_sort. eapply (@type_llift1 Sort_notion) ; eassumption.
      * lift_sort. eapply (@type_rlift1 Sort_notion) ; eassumption.
    + cbn. f_equal.
      * change (sPi1 (llift0 #|Γm| A1) (llift #|Γm| 1 B1) (llift0 #|Γm| p1))
          with (llift0 #|Γm| (sPi1 A1 B1 p1)).
        rewrite <- llift_subst.
        eapply nl_llift. assumption.
      * change (sPi1 (rlift0 #|Γm| A2) (rlift #|Γm| 1 B2) (rlift0 #|Γm| p2))
          with (rlift0 #|Γm| (sPi1 A2 B2 p2)).
        rewrite <- rlift_subst.
        eapply nl_rlift. assumption.

  (* Refl *)
  - destruct (IHsim1 Γ Γ1 Γ2) as [pA hpA].
    destruct (IHsim2 Γ Γ1 Γ2) as [pu hpu].
    exists (optCongRefl pA pu).
    intros Γm U1 U2 hm h1 h2.
    ttinv h1. ttinv h2.
    specialize (hpA _ _ _ hm h0 h5).
    specialize (hpu _ _ _ hm h h3).
    assert (s0 = s).
    { destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
      cleannl. eapply sorts_in_sort ; eassumption.
    } subst.
    eapply type_rename.
    + eapply opt_CongRefl ; eassumption.
    + cbn. f_equal.
      * change (nlEq (nl (llift0 #|Γm| A1)) (nl (llift0 #|Γm| u1)) (nl (llift0 #|Γm| u1)))
          with (nl (llift0 #|Γm| (sEq A1 u1 u1))).
        eapply nl_llift. assumption.
      * change (nlEq (nl (rlift0 #|Γm| A2)) (nl (rlift0 #|Γm| u2)) (nl (rlift0 #|Γm| u2)))
          with (nl (rlift0 #|Γm| (sEq A2 u2 u2))).
        eapply nl_rlift. assumption.

  (* Ax *)
  - case_eq (lookup_glob Σ id).
    + (* The axiom is in the global context *)
      intros ty eq.
      exists (sHeqRefl ty (sAx id)).
      intros Γm U1 U2 hm h1 h2.
      assert (h1' : Σ ;;; Γ ,,, Γm |-i sAx id : llift0 #|Γm| U1).
      { change (sAx id) with (llift0 #|Γm| (sAx id)).
        eapply type_llift0 ; eassumption.
      }
      assert (h2' : Σ ;;; Γ ,,, Γm |-i sAx id : rlift0 #|Γm| U2).
      { change (sAx id) with (rlift0 #|Γm| (sAx id)).
        eapply type_rlift0 ; eassumption.
      }
      pose proof (uniqueness hg h1' h2').
      destruct (istype_type hg h1).
      destruct (istype_type hg h2).
      eapply type_rename.
      * eapply type_HeqRefl' ; try assumption.
        econstructor ; try eassumption.
        eapply typing_wf. eassumption.
      * cbn. ttinv h1'. ttinv h2'. subst.
        f_equal.
        -- rewrite h0 in eq. inversion eq. subst. assumption.
        -- rewrite h4 in eq. inversion eq. subst. assumption.
    + (* The axiom isn't declared. We return garbage. *)
      intro neq.
      exists (sRel 0).
      intros Γm U1 U2 hm h1 h2.
      exfalso. ttinv h1.
      rewrite h0 in neq. discriminate neq.

  Unshelve.
  all: cbn ; try rewrite !length_cat ; try exact nAnon ; mylia.
Defined.

Corollary trel_to_heq :
  forall {Σ} Γ {t1 t2 : sterm},
    type_glob Σ ->
    t1 ∼ t2 ->
    ∑ p,
      forall T1 T2,
        Σ ;;; Γ |-i t1 : T1 ->
        Σ ;;; Γ |-i t2 : T2 ->
        Σ ;;; Γ |-i p : sHeq T1 t1 T2 t2.
Proof.
  intros Σ Γ t1 t2 hg h.
  destruct (trel_to_heq' hg h Γ [] []) as [p hp].
  exists p. intros T1 T2 h1 h2. specialize (hp _ _ _ (mixnil _ _) h1 h2).
  cbn in hp. rewrite !llift00, !rlift00 in hp.
  apply hp.
Defined.

Lemma inrel_lift :
  forall {t t'},
    t ⊏ t' ->
    forall n k, lift n k t ⊏ lift n k t'.
Proof.
  intros t t'. induction 1 ; intros m k.
  all: try (cbn ; now constructor).
  cbn. destruct (k <=? x) ; now constructor.
Defined.

Lemma inrel_subst :
  forall {t t'},
    t ⊏ t' ->
    forall {u u'},
      u ⊏ u' ->
      forall n, t{ n := u } ⊏ t'{ n := u' }.
Proof.
  intros t t'. induction 1 ; intros v1 v2 hu m.
  all: try (cbn ; constructor ; easy).
  cbn. destruct (m ?= x).
  - now apply inrel_lift.
  - constructor.
  - constructor.
Defined.

Lemma inrel_nl :
  forall {u u' v},
    u ⊏ u' ->
    nl u = nl v ->
    v ⊏ u'.
Proof.
  intros u u' v h eq.
  revert v eq. induction h.
  all: intros w eq.
  2:{ constructor. eapply IHh. assumption. }
  all: destruct w ; try discriminate eq.
  all: cbn in eq ; inversion eq ; now constructor.
Defined.

Lemma trel_lift :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall n k, lift n k t1 ∼ lift n k t2.
Proof.
  intros t1 t2. induction 1 ; intros n k.
  all: try (cbn ; now constructor).
  cbn. destruct (k <=? x) ; now constructor.
Defined.

Lemma trel_subst :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {u1 u2},
      u1 ∼ u2 ->
      forall n, t1{ n := u1 } ∼ t2{ n := u2 }.
Proof.
  intros t1 t2. induction 1 ; intros m1 m2 hu n.
  all: try (cbn ; constructor ; easy).
  unfold subst. destruct (n ?= x).
  - now apply trel_lift.
  - apply trel_Rel.
  - apply trel_Rel.
Defined.

(* Reflexivity is restricted to the syntax that makes sense in ETT. *)
Lemma trel_refl :
  forall {t},
    Xcomp t ->
    t ∼ t.
Proof.
  intros t h. dependent induction h.
  all: constructor. all: assumption.
Defined.

Lemma inrel_refl :
  forall {t},
    Xcomp t ->
    t ⊏ t.
Proof.
  intros t h. dependent induction h.
  all: constructor. all: assumption.
Defined.

Lemma trel_sym : forall {t1 t2}, t1 ∼ t2 -> t2 ∼ t1.
Proof.
  intros t1 t2. induction 1 ; (now constructor).
Defined.

Lemma inversion_trel_transport :
  forall {A B p t1 t2},
    sTransport A B p t1 ∼ t2 ->
    t1 ∼ t2.
Proof.
  intros A B p t1 t2 h.
  dependent induction h.
  - assumption.
  - constructor. eapply IHh.
Defined.

Lemma trel_trans :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {t3},
      t2 ∼ t3 ->
      t1 ∼ t3.
Proof.
  intros t1 t2. induction 1 ; intros t3 h.
  all: try (
    dependent induction h ; [
      constructor ; eapply IHh ; assumption
    | now constructor
    ]
  ).
  - constructor. now apply IHX.
  - apply IHX. eapply inversion_trel_transport. eassumption.
Defined.

Reserved Notation " Γ ≈ Δ " (at level 19).

Inductive crel : scontext -> scontext -> Type :=
| crel_empty : nil ≈ nil
| crel_snoc Γ Δ t u : Γ ≈ Δ -> t ∼ u -> (Γ ,, t) ≈ (Δ ,, u)

where " Γ ≈ Δ " := (crel Γ Δ).

Reserved Notation " Γ ⊂ Γ' " (at level 19).

Inductive increl : scontext -> scontext -> Type :=
| increl_empty : nil ⊂ nil
| increl_snoc Γ Γ' T T' :
    Γ ⊂ Γ' -> T ⊏ T' -> (Γ ,, T) ⊂ (Γ' ,, T')

where " Γ ⊂ Γ' " := (increl Γ Γ').

(*! Notion of translation *)
Definition trans Σ Γ A t Γ' A' t' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  t ⊏ t' *
  (Σ ;;; Γ' |-i t' : A').

End Fundamental.

Notation " Γ ≈ Δ " := (crel Γ Δ) (at level 19).

Notation " Γ ⊂ Γ' " := (increl Γ Γ') (at level 19).

Notation " Σ ;;;; Γ' ⊢ [ t' ] : A' ∈ ⟦ Γ ⊢ [ t ] : A ⟧ " :=
  (trans Σ Γ A t Γ' A' t')
    (at level 7) : i_scope.

Definition ctxtrans `{Sort_notion : Sorts.notion} Σ Γ Γ' :=
  Γ ⊂ Γ' * (wf Σ Γ').

Notation " Σ |--i Γ' ∈ ⟦ Γ ⟧ " := (ctxtrans Σ Γ Γ') (at level 7) : i_scope.

Section Head.

Context `{Sort_notion : Sorts.notion}.

(* Notion of head *)
Inductive head_kind :=
| headRel
| headSort (s : sort)
| headProd
| headLambda
| headApp
| headSum
| headPi1
| headPi2
| headEq
| headRefl
| headJ
| headTransport
| headHeq
| headOther
.

Definition head (t : sterm) : head_kind :=
  match t with
  | sRel x => headRel
  | sSort s => headSort s
  | sProd n A B => headProd
  | sLambda n A B t => headLambda
  | sApp u A B v => headApp
  | sSum _ _ _ => headSum
  | sPi1 _ _ _ => headPi1
  | sPi2 _ _ _ => headPi2
  | sEq A u v => headEq
  | sRefl A u => headRefl
  | sJ A u P w v p => headJ
  | sTransport A B p t => headTransport
  | sHeq A a B b => headHeq
  (* We actually only care about type heads in the source *)
  | _ => headOther
  end.

Inductive transport_data :=
| trd (T1 T2 p : sterm).

Definition transport_data_app (td : transport_data) (t : sterm) : sterm :=
  match td with
  | trd T1 T2 p => sTransport T1 T2 p t
  end.

Definition transport_seq := list transport_data.

Definition transport_seq_app (tr : transport_seq) (t : sterm) : sterm :=
  List.fold_right transport_data_app t tr.

Lemma trel_transport_seq :
  forall {A A'},
    A ⊏ A' ->
    ∑ A'' (tseq : transport_seq),
      (head A'' = head A) *
      (A' = transport_seq_app tseq A'') *
      (A ⊏ A'').
Proof.
  intros A A' h.
  induction h.
 all : try (eexists ; exists nil ; split;  [split ; [idtac | reflexivity]| idtac]; [reflexivity | now constructor ]).

  destruct IHh as [A'' [tseq [[hh he] hsub]]].
  exists A'', (trd T1 T2 p :: tseq). split ; [split | idtac].
  assumption.
  cbn. now f_equal.
  assumption.
Defined.

(* We only need it for heads in the source *)
Inductive type_head : head_kind -> Type :=
| type_headSort s : type_head (headSort s)
| type_headProd : type_head headProd
| type_headSum : type_head headSum
| type_headEq : type_head headEq
.

(* Maybe a waste to have it twice in the same file.
   Since it usually follows ttinv, maybe it should be
   provided in the same file and used automatically.
 *)
Ltac cleannl :=
  let inv h :=
    inversion h ; subst ; clear h
  in
  let aux t h :=
    destruct t ; cbn in h ; try discriminate h ; inv h
  in
  repeat match goal with
  | h : context [ nl (sSort _) ] |- _ => cbn in h
  | h : context [ nl (sProd _ _ _) ] |- _ => cbn in h
  | h : context [ nl (sSum _ _ _) ] |- _ => cbn in h
  | h : nlSort _ = nlSort _ |- _ => inv h
  | h : nlProd _ _ = nlProd _ _ |- _ => inv h
  | h : nlSum _ _ = nlSum _ _ |- _ => inv h
  | h : nl ?t = nlSort _ |- _ => aux t h
  | h : nlSort _ = nl ?t |- _ => aux t h
  | h : nlProd _ _ = nl ?t |- _ => aux t h
  | h : nl ?t = nlProd _ _ |- _ => aux t h
  | h : nlSum _ _ = nl ?t |- _ => aux t h
  | h : nl ?t = nlSum _ _ |- _ => aux t h
  end.

Lemma inversion_transportType :
  forall {Σ tseq Γ' A' T},
    type_glob Σ ->
    type_head (head A') ->
    Σ ;;; Γ' |-i transport_seq_app tseq A' : T ->
    exists s,
      (Σ ;;; Γ' |-i A' : sSort s) /\
      (Σ ;;; Γ' |-i T : sSort (Sorts.succ s)).
Proof.
  intros Σ tseq. induction tseq ; intros Γ' A' T hg hh ht.

  - cbn in *. destruct A' ; try (now inversion hh).
    + exists (Sorts.succ s). split.
      * apply type_Sort. apply (typing_wf ht).
      * ttinv ht. cleannl. eapply type_Sort. eapply typing_wf. eassumption.
    + ttinv ht. cleannl.
      exists (Sorts.prod_sort s1 s2). split.
      * now apply type_Prod.
      * eapply type_Sort. eapply typing_wf. eassumption.
    + ttinv ht. cleannl.
      exists (Sorts.sum_sort s1 s2). split.
      * now apply type_Sum.
      * eapply type_Sort. eapply typing_wf. eassumption.
    + ttinv ht. cleannl.
      exists (eq_sort s). split.
      * now apply type_Eq.
      * eapply type_Sort. eapply typing_wf. eassumption.

  - destruct a. cbn in ht.
    change (fold_right transport_data_app A' tseq)
      with (transport_seq_app tseq A') in ht.
    ttinv ht.
    destruct (IHtseq Γ' A' T1 hg hh h) as [s' [hAs hT1s]].
    exists s'. split.
    + assumption.
    + pose proof (uniqueness hg h1 hT1s) as hs.
      cbn in hs. inversion hs. subst.
      eapply rename_typed ; try eapply h4 ; try eassumption ; try reflexivity.
      eapply typing_wf. eassumption.
Defined.

Lemma choose_type' :
  forall {Σ A A' t t'} Γ',
    type_glob Σ ->
    type_head (head A) ->
    A ⊏ A' ->
    t ⊏ t' ->
    ∑ A'',
      (∑ t'',
         (t ⊏ t'') *
         (A ⊏ A'') *
         (Σ ;;; Γ' |-i t' : A' -> Σ;;; Γ' |-i t'' : A'')) *
      (head A'' = head A).
Proof.
  intros Σ A A' t t' Γ' hg hth hA ht.
  destruct (trel_transport_seq hA) as [A'' [tseq [[hh heq] hrel]]].
  exists A''. split.
  - case_eq (Equality.eq_term A' A'').
    + intro eq. exists t'. repeat split ; try assumption.
      intro h. eapply type_rename ; try eassumption.
      eapply Equality.eq_term_spec. assumption.
    + intros _.
      assert (simA : A' ∼ A'').
      { apply trel_sym.
        eapply trel_trans.
        - apply trel_sym. apply inrel_trel. eassumption.
        - apply inrel_trel. assumption.
      }
      { destruct (trel_to_heq Γ' hg simA) as [p hp].
        exists (optTransport A' A'' (optHeqToEq p) t').
        repeat split.
        + apply inrel_optTransport. assumption.
        + assumption.
        + intro h.
          rewrite heq in h.
          destruct (istype_type hg h) as [s hs].
          assert (hth' : type_head (head A'')) by (now rewrite hh).
          destruct (inversion_transportType hg hth' hs) as [s' [h' hss']].
          specialize (hp (sSort s) (sSort s)).
          rewrite <- heq in hs.
          assert (hAs : Σ ;;; Γ' |-i A'' : sSort s).
          { cut (s' = s).
            - intro. subst. assumption.
            - eapply sorts_in_sort ; try eassumption.
              apply type_Sort. apply (typing_wf h').
          }
          specialize (hp hs hAs).
          pose proof (opt_sort_heq hg hp) as hq.
          destruct (istype_type hg hp) as [? hEq].
          ttinv hEq.
          eapply opt_Transport ; try eassumption.
          subst. assumption.
      }
  - assumption.
Defined.

Lemma choose_type :
  forall {Σ Γ A t Γ' A' t'},
    type_glob Σ ->
    type_head (head A) ->
    Σ ;;;; Γ' ⊢ [ t' ] : A' ∈ ⟦ Γ ⊢ [t] : A ⟧ ->
    ∑ A'',
      (∑ t'', Σ ;;;; Γ' ⊢ [ t'' ] : A'' ∈ ⟦ Γ ⊢ [t] : A ⟧) *
      (head A'' = head A).
Proof.
  intros Σ Γ A t Γ' A' t' hg htt [[[hΓ hA] ht] h].
  destruct (choose_type' Γ' hg htt hA ht) as [A'' [[t'' [[? ?] hh]] ?]].
  exists A''. split.
  - exists t''. repeat split ; try assumption.
    apply hh. assumption.
  - assumption.
Defined.

Lemma change_type :
  forall {Σ Γ A t Γ' A' t' s A''},
    type_glob Σ ->
    Σ ;;;; Γ' ⊢ [ t' ] : A' ∈ ⟦ Γ ⊢ [t] : A ⟧ ->
    Σ ;;;; Γ' ⊢ [ A'' ] : sSort s ∈ ⟦ Γ ⊢ [A] : sSort s ⟧ ->
    ∑ t'', Σ ;;;; Γ' ⊢ [ t'' ] : A'' ∈ ⟦ Γ ⊢ [t] : A ⟧.
Proof.
  intros Σ Γ A t Γ' A' t' s A'' hg [[[rΓ' rA'] rt'] ht'] [[[rΓ'' _] rA''] hA''].
  assert (simA : A' ∼ A'').
  { eapply trel_trans.
    - eapply trel_sym. eapply inrel_trel. eassumption.
    - eapply inrel_trel. eassumption.
  }
  destruct (trel_to_heq Γ' hg simA) as [p hp].
  case_eq (Equality.eq_term A' A'').
  - intro eq. exists t'. repeat split ; try assumption.
    eapply type_rename ; try eassumption.
    eapply Equality.eq_term_spec. assumption.
  - exists (optTransport A' A'' (optHeqToEq p) t').
    repeat split.
    + assumption.
    + assumption.
    + apply inrel_optTransport. assumption.
    + destruct (istype_type hg ht') as [s2 hA'].
      specialize (hp (sSort s2) (sSort s) hA' hA'').
      destruct (istype_type hg hp) as [s1 hheq].
      assert (Σ ;;; Γ' |-i sSort s : sSort (Sorts.succ s)).
      { apply type_Sort. apply (typing_wf hp). }
      ttinv hheq.
      assert (s2 = s).
      { eapply sorts_in_sort ; eassumption. } subst.
      eapply opt_Transport ; try assumption.
      eapply opt_HeqToEq ; eassumption.
Defined.

End Head.