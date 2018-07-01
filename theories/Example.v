(* -*- coq-prog-args: ("-emacs" "-type-in-type") -*- *)

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker.
From Translation Require Import util Sorts SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Quotes Translation FinalTranslation
                                FullQuote ExamplesUtil.

Open Scope string_scope.
Open Scope x_scope.

(*! EXAMPLE 1 (NEW) *)

Fail Definition pseudoid := fun (A B : Type) (e : A = B) (x : A) => x : B.

(* Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}. *)
Quote Definition pseudoid := (fun (A B : Type) (e : A = B) (x : A) => {! x !} : B).

Definition tm_pseudoid :=
  Eval lazy in fullquote (2 ^ 18) Σ [] pseudoid.

(* We actually just want the definition! *)
(* Quote Recursively Definition fold_pseudoid := pseudoid. *)
(* Definition tc_pseudoid := *)
(*   Eval lazy in *)
(*   let Σ := pair (Datatypes.fst fold_pseudoid) init_graph in *)
(*   let t := Datatypes.snd fold_pseudoid in *)
(*   match hnf Σ [] t with *)
(*   | Checked t => t *)
(*   | _ => tRel 0 *)
(*   end. *)

(*! EXAMPLE 1:
    λ A B e x ⇒ x : ∀ (A B : Type), A = B → A → B
    It uses reflection to be well-typed.
    It gets translated to
    λ A B e x ⇒ transport e x : ∀ (A B : Type), A = B → A → B.
*)

(* We begin with an ETT derivation *)

Definition tyl :=
  [ sSort tt ;
    sSort tt ;
    sEq (sSort tt) (sRel 1) (sRel 0) ;
    sRel 2 ;
    sRel 2
  ].

Definition ty : sterm := multiProd tyl.

Definition tm : sterm := multiLam tyl (sRel 0).

Fact tmty : Σi ;;; [] |-x tm : ty.
Proof.
  eapply type_multiLam.
  - constructor.
  - econstructor.
    + eapply type_Sort. constructor.
    + econstructor.
      * eapply type_Sort.
        repeat econstructor.
      * econstructor.
        -- eapply type_Eq.
           ++ repeat constructor.
              ** repeat econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
        -- econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ econstructor.
              ** refine (type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** eapply type_conv''.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                 --- cbn. eapply reflection.
                     instantiate (2 := sRel 1).
                     refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
  Unshelve.
  all: cbn; omega.
Defined.

(* Then we translate this ETT derivation to get an ITT term *)

Definition itt_tm : sterm.
  destruct (type_translation tmty istrans_nil) as [A [t h]].
  exact t.
Defined.

Definition itt_tm' := ltac:(let t := eval lazy in itt_tm in exact t).

Definition tc_tm : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm'.

Definition tc_tm' := ltac:(let t := eval lazy in tc_tm in exact t).

Make Definition coq_tm :=
  ltac:(
    let t := eval lazy in
             (match tc_tm' with
              | Success _ t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 2:
    λ A x ⇒ x : ∀ (A : Type), A → A
    It gets translated to itself.
*)

Definition tyl0 :=
  [ sSort tt ;
    sRel 0 ;
    sRel 1
  ].

Definition ty0 : sterm := multiProd tyl0.

Definition tm0 : sterm := multiLam tyl0 (sRel 0).

Lemma tmty0 : Σi ;;; [] |-x tm0 : ty0.
Proof.
  eapply type_multiLam.
  - constructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      * refine (type_Rel _ _ _ _ _).
        -- repeat econstructor.
        -- cbn. omega.
      * econstructor.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
  Unshelve. all: cbn; omega.
Defined.

Definition itt_tm0 : sterm.
  destruct (type_translation tmty0 istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_tm0' := ltac:(let t := eval lazy in itt_tm0 in exact t).

Definition tc_tm0 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm0'.

Definition tc_tm0' := ltac:(let t := eval lazy in tc_tm0 in exact t).

Make Definition coq_tm0 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm0' with
              | Success _ t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).


(*! EXAMPLE 3:
    nat
    It gets translated to itself.
*)

Lemma natty : Σi ;;; [] |-x sAx "nat" : sSort tt.
Proof.
  ettcheck.
Defined.

Definition itt_nat : sterm.
  destruct (type_translation natty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_nat' := ltac:(let t := eval lazy in itt_nat in exact t).

Definition tc_nat : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_nat'.

Definition tc_nat' := ltac:(let t := eval lazy in tc_nat in exact t).

Make Definition coq_nat :=
  ltac:(
    let t := eval lazy in
             (match tc_nat' with
              | Success _ t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 3':
    zero
    It gets translated to itself.
*)

Lemma zeroty : Σi ;;; [] |-x sAx "zero" : sAx "nat".
Proof.
  ettcheck.
Defined.

Definition itt_zero : sterm.
  destruct (type_translation zeroty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_zero' := ltac:(let t := eval lazy in itt_zero in exact t).

Definition tc_zero : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_zero'.

Definition tc_zero' := ltac:(let t := eval lazy in tc_zero in exact t).

Make Definition coq_zero :=
  ltac:(
    let t := eval lazy in
             (match tc_zero' with
              | Success _ t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 3'':
    succ zero
    It gets translated to itself.
*)

Definition sNat := sAx "nat".
Definition sZero := sAx "zero".
Definition sSucc n :=
  sApp (sAx "succ") sNat sNat n.

Lemma type_zero :
  forall {Γ},
    wf Σi Γ ->
    Σi ;;; Γ |-x sZero : sNat.
Proof.
  unfold sZero, sNat.
  intros Γ h.
  ettcheck.
Defined.

Lemma type_succ :
  forall {Γ n},
    Σi ;;; Γ |-x n : sNat ->
    Σi ;;; Γ |-x sSucc n : sNat.
Proof.
  unfold sSucc, sNat.
  intros Γ n h.
  pose proof (typing_wf h) as hw.
  ettcheck. assumption.
Defined.

Definition sOne := sSucc sZero.

Lemma onety : Σi ;;; [] |-x sOne : sNat.
Proof.
  unfold sOne. eapply type_succ. eapply type_zero. constructor.
Defined.

Definition itt_one : sterm.
  destruct (type_translation onety istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_one' := ltac:(let t := eval lazy in itt_one in exact t).

Definition tc_one : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_one'.

Definition tc_one' := ltac:(let t := eval lazy in tc_one in exact t).

Make Definition coq_one :=
  ltac:(
    let t := eval lazy in
             (match tc_one' with
              | Success _ t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).


(* (*! EXAMPLE 4.1: *)
(*     vcons one zero vnil *)
(*     It gets translated to itself (but checking takes a long time!). *)
(* *) *)

(* Open Scope type_scope. *)

(* Definition sVec A n := *)
(*   Apps (sAx "vec") [ (nNamed "A", sSort tt) ; (nAnon, sNat) ] (sSort tt) [ A ; n ]. *)

(* Definition sVnil A := *)
(*   sApp (sAx "vnil") *)
(*        (sSort tt) *)
(*        (sVec (sRel 0) sZero) *)
(*        A. *)

(* Definition sVcons A a n v := *)
(*   Apps *)
(*     (sAx "vcons") *)
(*     [ (nNamed "A", sSort tt) ; *)
(*       (nAnon, sRel 0) ; *)
(*       (nNamed "n", sNat) ; *)
(*       (nAnon, sVec (sRel 2) (sRel 0)) *)
(*     ] *)
(*     (sVec (sRel 3) (sSucc (sRel 1))) *)
(*     [ A ; a ; n ; v ]. *)

(* Lemma type_vec : *)
(*   forall {Γ A n}, *)
(*     Σi ;;; Γ |-x A : sSort tt -> *)
(*     Σi ;;; Γ |-x n : sNat -> *)
(*     Σi ;;; Γ |-x sVec A n : sSort tt. *)
(* Proof. *)
(*   unfold sVcons, sVec, sVnil, sOne, sSucc, sNat, sZero. *)
(*   intros Γ A n hA hn. *)
(*   pose proof (typing_wf hA) as hw. *)
(*   simpl. ettcheck. all: assumption. *)
(* Defined. *)

(* Lemma type_vnil : *)
(*   forall {Γ A}, *)
(*     Σi ;;; Γ |-x A : sSort tt -> *)
(*     Σi ;;; Γ |-x sVnil A : sVec A sZero. *)
(* Proof. *)
(*   unfold sVcons, sVec, sVnil, sSucc, sNat, sZero. *)
(*   intros Γ A h. simpl. *)
(*   pose proof (typing_wf h) as hw. *)
(*   Opaque lift. *)
(*   ettcheck. all: try assumption. *)
(*   - unfold sVec, sNat. simpl. ettcheck. *)
(*   - simpl. rewrite lift00. constructor. *)
(*     ettcheck. assumption. *)
(* Defined. *)

(* Transparent lift. *)

(* (* Lemma type_vcons : *) *)
(* (*   forall {Γ A a n v}, *) *)
(* (*     Σi ;;; Γ |-x A : sSort 0 -> *) *)
(* (*     Σi ;;; Γ |-x a : A -> *) *)
(* (*     Σi ;;; Γ |-x n : sNat -> *) *)
(* (*     Σi ;;; Γ |-x v : sVec A n -> *) *)
(* (*     Σi ;;; Γ |-x sVcons A a n v : sVec A (sSucc n). *) *)
(* (* Proof. *) *)
(* (*   unfold sVcons, sVec, sVnil, sSucc, sNat, sZero. *) *)
(* (*   intros Γ A a n v hA ha hn hv. *) *)
(* (*   pose proof (typing_wf ha) as hw. *) *)
(* (*   simpl. *) *)
(* (*   ettcheck. *) *)
(* (*   all: rewrite ?lift00. all: try eassumption. *) *)
(* (*   - *) *)

(* Definition vtest := sVcons sNat sOne sZero (sVnil sNat). *)

(* Lemma vtestty : Σi ;;; [] |-x vtest : sVec sNat sOne. *)
(* Proof. *)
(*   unfold vtest, sVcons, sVec, sVnil, sOne, sSucc, sNat, sZero. lazy. *)
(*   ettcheck. *)
(* Defined. *)

(* Definition itt_vtest : sterm. *)
(*   destruct (type_translation vtestty istrans_nil) as [A [t [_ h]]]. *)
(*   exact t. *)
(* Defined. *)

(* Definition itt_vtest' := ltac:(let t := eval lazy in itt_vtest in exact t). *)

(* Definition tc_vtest : tsl_result term := *)
(*   tsl_rec (2 ^ 18) Σ [] itt_vtest'. *)

(* Definition tc_vtest' := ltac:(let t := eval lazy in tc_vtest in exact t). *)

(* Make Definition coq_vtest := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_vtest' with *)
(*               | Success t => t *)
(*               | _ => tSort Universe.type0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)


(* (*! EXAMPLE 4.2: *)
(*     plus *)
(* *) *)
(* Definition snatrec P Pz Ps n := *)
(*   Apps *)
(*     (sAx "nat_rect") *)
(*     [ (nNamed "P", sNat ==> sSort 0) ; *)
(*       (nAnon, sApp (sRel 0) sNat (sSort 0) sZero) ; *)
(*       (nAnon, sProd (nNamed "n") sNat (sApp (sRel 2) sNat (sSort 0) (sRel 0) ==> sApp (sRel 2) sNat (sSort 0) (sSucc (sRel 0)))) ; *)
(*       (nNamed "n", sNat) *)
(*     ] *)
(*     (sApp (sRel 3) sNat (sSort 0) (sRel 0)) *)
(*     [ P ; Pz ; Ps ; n ]. *)

(* Definition plus n m := *)
(*   snatrec (sLambda (nNamed "n") sNat (sSort 0) sNat) *)
(*           m *)
(*           (multiLam [ sNat ; sNat ; sNat ] (sSucc (sRel 0))) *)
(*           n. *)

(* Definition cplus := *)
(*   sLambda (nNamed "n") sNat (sNat ==> sNat) *)
(*   (sLambda (nNamed "m") sNat sNat (plus (sRel 1) (sRel 0))). *)

(* Ltac ettcong := *)
(*   lazymatch goal with *)
(*   | |- ?Σ ;;; ?Γ |-x ?t = _ : ?T => *)
(*     lazymatch t with *)
(*     | sRel ?n => eapply eq_reflexivity *)
(*     | sSort _ => eapply eq_reflexivity *)
(*     | sProd _ _ _ => eapply cong_Prod *)
(*     | sLambda _ _ _ _ => eapply cong_Lambda *)
(*     | sApp _ _ _ _ => eapply cong_App *)
(*     | sSum _ _ _ => eapply cong_Sum *)
(*     | sPair _ _ _ _ => eapply cong_Pair *)
(*     | sPi1 _ _ _ => eapply cong_Pi1 *)
(*     | sPi2 _ _ _ => eapply cong_Pi2 *)
(*     | sEq _ _ _ => eapply cong_Eq *)
(*     | sRefl _ _ => eapply cong_Refl *)
(*     | sAx _ => eapply eq_reflexivity *)
(*     | _ => fail "No congruence rule for" t *)
(*     end *)
(*   | _ => fail "Not applicable" *)
(*   end. *)

(* Lemma xmeta_eq_conv : *)
(*   forall {Σ Γ A B T U}, *)
(*     Σ ;;; Γ |-x A = B : U -> *)
(*     T = U -> *)
(*     Σ ;;; Γ |-x A = B : T. *)
(* Proof. *)
(*   intros Σ Γ A B T U h e. destruct e. assumption. *)
(* Defined. *)

(* Ltac ettconvcheck1 := *)
(*   lazymatch goal with *)
(*   | |- ?Σ ;;; ?Γ |-x ?t = ?u : ?T => *)
(*     first [ *)
(*       eapply xmeta_eq_conv ; [ ettcong | lazy ; reflexivity ] *)
(*     | eapply eq_conv ; [ ettcong | .. ] *)
(*     (* | eapply meta_ctx_conv ; [ *) *)
(*     (*     eapply meta_conv ; [ ettintro | lazy ; try reflexivity ] *) *)
(*     (*   | cbn ; try reflexivity *) *)
(*     (*   ] *) *)
(*     ] *)
(*   | |- wf ?Σ ?Γ => first [ assumption | econstructor ] *)
(*   | |- sSort _ = sSort _ => first [ lazy ; reflexivity | shelve ] *)
(*   | |- type_glob _ => first [ assumption | glob ] *)
(*   | _ => fail "Not applicable" *)
(*   end. *)

(* Lemma plusty : Σi ;;; [] |-x cplus : sNat ==> sNat ==> sNat. *)
(* Proof. *)
(*   unfold cplus, plus, snatrec, sZero, sSucc, sNat, Arrow. simpl. *)
(*   (* ettcheck. *) *)
(*   (* - cbn. repeat ettconvcheck1. all: ettcheck. *) *)
(* Abort. *)

(* (*! EXAMPLE 4.? (more ambitious): *)
(*     rev A n m (v : vec A n) (acc : vec A m) : vec A (n + m) := *)
(*       vec_rect A ??? *)
(* *) *)