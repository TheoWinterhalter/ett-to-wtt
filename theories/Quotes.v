
Set Primitive Projections.
Set Universe Polymorphism.
Set Printing Universes.

Section Notations.

(* Inductive eq@{i} (A : Type@{i}) (a : A) : A -> Type@{i} :=  eq_refl : eq A a a. *)
(* Arguments eq {A} _ _. *)
(* Arguments eq_refl {A} a. *)

Axiom eq@{i} : forall {A : Type@{i}} (a : A), A -> Type@{i}.
Axiom eq_refl@{i} : forall {A : Type@{i}} (a : A), eq a a.

Notation "x = y :> A" := (@eq A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Notation "1" := (eq_refl _).

Axiom J@{i j} : forall {A : Type@{i}} {u} (P : forall (x : A), u = x -> Type@{j})
                  {v} (p : u = v) (w : P u (@eq_refl A u)), P v p.
Axiom Jβ@{i j} : forall {A : Type@{i}} {u} (P : forall (x : A), u = x -> Type@{j})
           (w : P u (@eq_refl A u)), J P (@eq_refl A u) w = w.
Axiom K@{i} : forall {A : Type@{i}} {x : A} (p : x = x), p = 1.
Axiom funext@{i j ij} : forall {A : Type@{i}} {B : A -> Type@{j}} {f g : forall (x : A), B x},
    (forall x, f x = g x) -> eq@{ij} f g.

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x y : A} (p : x = y) (u : P x) : P y
  := J (fun y _ => P y) p u.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Definition inverse@{i} {A : Type@{i}} {x y : A} (p : x = y) : y = x
  := transport (fun x' => x' = x) p 1.

Definition concat@{i} {A : Type@{i}} {x y z : A} (p : x = y) (q : y = z) : x = z
  := transport (eq x) q p.

Notation "p @ q" := (concat p q) (at level 20).
Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Definition ap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y} (p : x = y)
  : f x = f y
  := transport (fun y => f x = f y) p 1.

Definition coe@{i i1} {A B : Type@{i}} (p : eq@{i1} A B) : A -> B
  := fun x => transport (fun T => T) p x.
(* Axiom coe@{i i1} : forall {A B : Type@{i}} (p : eq@{i1} A B), A -> B. *)

Definition transportβ@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x} (u : P x)
  : transport@{i j} P 1 u = u
  := Jβ@{i j} (fun x _ => P x)u.

Definition coeβ@{i i1} {A : Type@{i}} (x : A)
  : coe@{i i1} 1 x = x
  := transportβ (fun T => T) x.
(* . Admitted. *)

Tactic Notation "etransitivity" := refine (_ @ _).
Tactic Notation "symmetry" := refine (_^).
Tactic Notation "reflexivity" := exact 1.




(* Record sigT@{i j} {A : Type@{i}} (P : A -> Type@{j}) : Type@{max(i,j)} := existT *)
(*   { projT1 : A ; projT2 : P projT1 }. *)

(* Arguments existT {A} P _ _. *)
(* Arguments projT1 {A P} _. *)
(* Arguments projT2 {A P} _. *)


Axiom sigT@{i j} : forall {A : Type@{i}} (P : A -> Type@{j}), Type@{max(i,j)}.
Axiom existT@{i j} : forall {A : Type@{i}} (P : A -> Type@{j}) (x : A) (y : P x), sigT P.
Axiom projT1@{i j} : forall {A : Type@{i}} {P : A -> Type@{j}} (w : sigT P), A.
Axiom projT2@{i j} : forall {A : Type@{i}} {P : A -> Type@{j}} (w : sigT P), P (projT1 w).

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Axiom projT1β@{i j} : forall {A : Type@{i}} (P : A -> Type@{j}) x y,
    eq@{i} (existT P x y).1 x.
Axiom projT2β@{i j} : forall {A : Type@{i}} (P : A -> Type@{j}) x y,
    eq@{j} (transport P (projT1β _ _ _) (existT P x y).2) y.
Axiom Ση@{i j ij} : forall {A : Type@{i}} (P : A -> Type@{j}) (z : {x : A & P x}),
    eq@{ij} (z.1; z.2) z.

Definition sigT_rect@{i j ij k} {A : Type@{i}} (P : A -> Type@{j})
           (Q : {x : A & P x} -> Type@{k})
           (H : forall x p, Q (existT P x p))
  : forall s , Q s.
Proof.
  intro s.
  exact (Ση@{i j ij} P s # H s.1 s.2).
Defined.

Definition sigT_rec@{i j k} {A : Type@{i}} (P : A -> Type@{j})
           (Q : Type@{k})
           (H : forall x, P x -> Q)
  : {x : A & P x} -> Q
  := fun z => H z.1 z.2.
  (* := sigT_rect@{i j ij k} P (fun _ => Q) H. *)

Tactic Notation "exists" uconstr(x) := refine (existT _ x _).



Definition heq@{i i1} {A : Type@{i}} (a : A) {B : Type@{i}} (b : B) :=
  @sigT (eq@{i1} A B) (fun e => coe e a = b).

Notation "A ≅ B" := (heq A B) (at level 20).

Definition coeβ'@{i i1} {A : Type@{i}} (e : A = A) (x : A) : coe@{i i1} e x = x.
Proof.
  refine (_ @ coeβ@{i i1} x).
  refine (transport (fun e => _ = coe e x) _ 1).
  apply K.
Defined.

Lemma heq_to_eq@{i i1} {A : Type@{i}} {u v : A}
  : heq@{i i1} u v -> u = v.
Proof.
  intros h.
  refine (_ @ h.2). symmetry.
  apply coeβ'.
Defined.

Lemma eq_to_heq@{i i1} {A : Type@{i}} {u v : A}
  : u = v -> heq@{i i1} u v.
Proof.
  intros h. exists 1.
  refine (_ @ h). apply coeβ.
Defined.

Lemma heq_refl@{i i1} {A : Type@{i}} (a : A) : heq@{i i1} a a.
Proof.
  exists 1. apply coeβ.
Defined.

Lemma heq_sym@{i i1} {A B : Type@{i}} (a : A) (b : B)
  : heq@{i i1} a b -> heq@{i i1} b a.
Proof.
  apply sigT_rec@{i1 i i1}.
  intro e; revert b.
  refine (J (fun B p => forall b, coe p a = b -> b ≅ a) e _).
  intros b H.  exists 1.
  etransitivity. apply coeβ.
  etransitivity. symmetry; eassumption. apply coeβ.
Defined.

(* Opaque transport coe heq inverse concat coeβ coeβ'. *)
(* Eval compute in heq_sym. *)


Lemma heq_trans@{i i1} {A B C : Type@{i}} (a : A) (b : B) (c : C)
  : heq@{i i1} a b -> b ≅ c -> a ≅ c.
Proof.
  refine (sigT_rec@{i1 i i1} _ _ _); intros p1 e1.
  refine (sigT_rec@{i1 i i1} _ _ _); intros p2 e2.
  revert p2 b c e1 e2.
  refine (J (fun B p1 => forall p2 b c,
                 coe p1 a = b -> coe p2 b = c -> a ≅ c) _ _).
  intros p2 b.
  refine (J (fun B p2 => forall c,
                 coe 1 a = b -> coe p2 b = c -> a ≅ c) _ _).
  intros c e1 e2. 
  exists 1. etransitivity. eassumption. etransitivity. 2: eassumption.
  symmetry; apply coeβ.
Defined.


Definition heq_type_eq@{i i1} {A : Type@{i}} {u : A} {B : Type@{i}} {v : B}
  : heq@{i i1} u v -> A = B
  := projT1.

Lemma heq_transport@{i i1} {T T' : Type@{i}} (p : T = T') (t : T)
  : t ≅ coe@{i i1} p t.
Proof.
  exists p. reflexivity.
Defined.

Lemma heq_apD@{i i1 j j1} {A : Type@{i}} {B : A -> Type@{j}}
      (f : forall x, B x) {x y : A} (e : x = y)
  : heq@{j j1} (f x) (f y).
Proof.
  refine (transport (fun y => heq@{j j1} (f x) (f y)) e _).
  apply heq_refl.
Defined.



Definition Pack@{i i1} (A1 A2 : Type@{i}) : Type@{i1}
  := exists (x1 : A1)(x2 : A2), heq@{i i1} x1 x2.
(* . Admitted. *)
Definition pack@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: heq @{i i1} x1 x2)
  : Pack@{i i1} A1 A2
  := (x1; (x2; e)).
(* . Admitted. *)
Definition ProjT1@{i i1} {A1 A2 : Type@{i}} (z : Pack@{i i1} A1 A2) : A1
  := z.1.
(* . Admitted. *)
Definition ProjT2@{i i1} {A1 A2 : Type@{i}} (z : Pack@{i i1} A1 A2) : A2
  := z.2.1.
(* . Admitted. *)
Definition ProjTe@{i i1} {A1 A2 : Type@{i}} (z : Pack@{i i1} A1 A2)
  : heq@{i i1} (ProjT1 z) (ProjT2 z)
  := z.2.2.
(* . Admitted. *)


Definition transport_sigma_const@{i j ij} {X A : Type@{i}} {B : A -> X -> Type@{j}}
           {x x'} (p : x = x' :> X) (u : exists a, B a x)
  : transport@{i ij} (fun x => sigT@{i j} (fun a => B a x)) p u
    = (u.1; transport (B u.1) p u.2).
Proof.
  revert u.
  refine (J (fun x' p => forall u, transport (fun x => exists a, B a x) p u
                           = (u.1; transport (B u.1) p u.2)) p _);
    clear x' p.
  intro u. refine (transportβ _ _ @ _).
  refine (transport (fun u2 => u = (u.1; u2)) (transportβ (B u.1) u.2)^ _).
  symmetry; apply Ση.
Defined.
           

Definition ProjT1β@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: x1 ≅ x2)
 : ProjT1 (pack@{i i1} x1 x2 e) = x1
  := projT1β _ _ _.
(* . Admitted. *)

Definition ProjT2β@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: x1 ≅ x2)
 : ProjT2 (pack@{i i1} x1 x2 e) = x2.
Proof.
  unfold ProjT2.
  pose proof ((transport_sigma_const _ _)^
              @ projT2β (fun x1 => exists x2, heq x1 x2) x1 (x2; e)).
  refine (_ @ ap projT1 X @ projT1β _ _ _).
  symmetry; eapply projT1β.
Defined.
(* Admitted. *)

(* Definition ProjTeβ@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: x1 ≅ x2) *)
(*  : ProjTe (pack@{i i1} x1 x2 e) ≅ e. *)


Lemma heq_to_eq_fam@{i i1 j j1 j2 ij1} (A : Type@{i})
      (B1 : A -> Type@{j}) (B2 : A -> Type@{j})
      (hB : forall (p : Pack@{i i1} A A), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : eq@{ij1} B1 B2.
Proof.
  apply funext. intro x.
  refine (_ @ heq_to_eq (hB (pack x x (heq_refl x))) @ _).
  all: apply ap. symmetry; apply ProjT1β. apply ProjT2β.
Defined.

Lemma heq_to_eq_fam'@{i i1 i2 j j1 j2 ij1 k i1j2k} {A1 A2 : Type@{i}}
      {B1 : A1 -> Type@{j}} {B2 : A2 -> Type@{j}}
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (P : forall (A : Type@{i})(B : A -> Type@{j}), Type@{k})
      (P1 : P A1 B1)
  : P A2 B2.
Proof.
  revert B2 hB. refine (transport@{i1 i1j2k} (fun A2: Type@{i} => forall B2 : A2 -> Type@{j}, (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) -> P A2 B2) (heq_to_eq hA) _).
  intros B2 hB. refine (transport@{ij1 k} _ _ P1). apply funext; intro x.
  refine (_ @ heq_to_eq (hB (pack x x (heq_refl x))) @ _).
  all: apply ap. symmetry; apply ProjT1β. apply ProjT2β.
Defined.


Lemma cong_prod@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : @heq@{ij1 ij2} Type@{ij} (forall x : A1, B1 x) Type@{ij} (forall y : A2, B2 y).
Proof.
  refine (heq_to_eq_fam'@{i i1 i2 j j1 j2 ij1 ij2 ij2} hA hB (fun A2 B2 => @heq@{ij1 ij2} Type@{ij} (forall x : A1, B1 x) Type@{ij} (forall y : A2, B2 y)) _). eapply heq_refl.
Defined.


Lemma cong_lambda@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (f1 : forall x, B1 x) (f2 : forall x, B2 x)
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hf : forall (p : Pack@{i i1} A1 A2), f1 (ProjT1 p) ≅ f2 (ProjT2 p))
  : heq@{ij ij1} (fun x => f1 x) (fun x => f2 x).
Proof.
  revert f1 f2 hf.
  refine (heq_to_eq_fam'@{i i1 i2 j j1 j2 ij1 ij2 ij2} hA hB (fun A2 B2 =>   forall (f1 : forall x : A1, B1 x) (f2 : forall x : A2, B2 x), (forall p : Pack@{i i1} A1 A2, f1 (ProjT1@{i i1} p) ≅ f2 (ProjT2@{i i1} p)) -> (fun x : A1 => f1 x) ≅ (fun x : A2 => f2 x) ) _).
  intros f1 f2 hf. apply eq_to_heq. apply funext; intro x.
  specialize (hf (pack x x (heq_refl x))).
  assert (hf' : f1 x ≅ f2 x). {
    eapply heq_trans. 2:eapply heq_trans.
    2: exact hf.
    apply heq_apD@{i i1 j j1}. symmetry; apply ProjT1β.
    apply heq_apD@{i i1 j j1}. apply ProjT2β. }
  apply heq_to_eq, hf'.
Defined.


Lemma cong_app@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (f1 : forall x, B1 x) (f2 : forall x, B2 x)
      (u1 : A1) (u2 : A2)
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hf : heq@{ij ij1} f1 f2)
      (hu : u1 ≅ u2)
  : f1 u1 ≅ f2 u2.
Proof.
  apply heq_to_eq in hA.
  revert B2 hB f2 hf u2 hu.
  refine (transport@{i1 ij1} (fun A2 : Type@{i} =>  forall B2 : A2 -> Type@{j},
  (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) ->
  forall (f2 : forall x : A2, B2 x), f1 ≅ f2 -> forall (u2 : A2), u1 ≅ u2 -> f1 u1 ≅ f2 u2) hA _).
  clear A2 hA; intros B2 hB.
  apply heq_to_eq_fam in hB.
  refine (transport@{ij1 ij2} (fun B2 : A1 -> Type@{j} =>  forall (f2 : forall x : A1, B2 x),
  f1 ≅ f2 -> forall u2 : A1, u1 ≅ u2 -> f1 u1 ≅ f2 u2) hB _).
  clear hB B2; intros f2 hf.
  apply heq_to_eq in hf.
  refine (transport@{ij ij1} (fun f2 => forall u2 : A1, u1 ≅ u2 -> f1 u1 ≅ f2 u2) hf _).
  clear f2 hf; intros u2 hu. 
  apply heq_to_eq in hu.
  refine (transport@{ij ij1} (fun u2 => f1 u1 ≅ f1 u2) hu _).
  apply heq_refl.
Defined.

Lemma cong_sum@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : @heq@{ij1 ij2} Type@{ij} (sigT B1) Type@{ij} (sigT B2).
Proof.
  exists 1. etransitivity. eapply coeβ.
  apply heq_to_eq in hA.
  revert B2 hB.
  refine (transport@{i1 ij1} (fun A2 : Type@{i} => forall B2 : A2 -> Type@{j},
                     (forall p, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
                     @eq Type@{ij} (sigT B1) (sigT B2)) hA _).
  intros B2 hB. apply heq_to_eq_fam in hB.
  refine (ap@{ij1 _} (B:=Type@{ij})(fun B : A1 -> Type@{j} => sigT B) hB).
Defined.

Lemma cong_pair@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (u1 : A1) (u2 : A2) (v1 : B1 u1) (v2 : B2 u2)
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : u1 ≅ u2 ->
    v1 ≅ v2 ->
    heq@{ij ij1} (existT B1 u1 v1) (existT B2 u2 v2).
Proof.
  revert B2 hB u2 v2.
apply heq_to_eq in hA.
  refine (transport@{i1 ij1} (fun A2 : Type@{i} =>  forall B2 : A2 -> Type@{j},
  (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) ->
  forall (u2 : A2) (v2 : B2 u2), u1 ≅ u2 -> v1 ≅ v2 -> (u1; v1) ≅ (u2; v2)) hA _).
  clear A2 hA; intros B2 hB.
  apply heq_to_eq_fam in hB.
  refine (transport@{ij1 ij2} (fun B2 : A1 -> Type@{j} => forall (u2 : A1) (v2 : B2 u2),
                                 u1 ≅ u2 -> v1 ≅ v2 -> (u1; v1) ≅ (u2; v2)) hB _).
  clear hB B2; intros u2 v2 hu; revert v2.
  apply heq_to_eq in hu.
  refine (transport@{ij ij1} (fun u2 => forall v2 : B1 u2, v1 ≅ v2 -> (u1; v1) ≅ (u2; v2)) hu _).
  clear u2 hu; intros v2 hv. 
  apply heq_to_eq in hv.
  refine (transport@{ij ij1} (fun v2 => (u1; v1) ≅ (u1; v2)) hv _).
  apply heq_refl.
Defined.

Lemma cong_pi1@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (p1 : sigT B1) (p2 : sigT B2)
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : heq@{ij ij1} p1 p2 -> p1.1 ≅ p2.1.
Proof.
  apply heq_to_eq in hA.
  revert B2 hB p2.
  refine (transport@{i1 ij1} (fun A2 : Type@{i} =>  forall B2 : A2 -> Type@{j},
    (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) ->
  forall (p2 : {x : _ & B2 x}), p1 ≅ p2 -> p1.1 ≅ p2.1) hA _).
  clear A2 hA; intros B2 hB.
  apply heq_to_eq_fam in hB.
  refine (transport@{ij1 ij2} (fun B2 : A1 -> Type@{j} => forall (p2 : {x : A1 & B2 x}), p1 ≅ p2 -> p1.1 ≅ p2.1) hB _).
  clear hB B2; intros p2 hp.
  apply heq_to_eq in hp.
  refine (transport@{ij ij1} (fun p2 => p1.1 ≅ p2.1) hp _).
  apply heq_refl.
Defined.

Lemma cong_pi2@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (p1 : sigT B1) (p2 : sigT B2)
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : heq@{ij ij1} p1 p2 -> p1.2 ≅ p2.2.
Proof.
  apply heq_to_eq in hA.
  revert B2 hB p2.
  refine (transport@{i1 ij1} (fun A2 : Type@{i} =>  forall B2 : A2 -> Type@{j},
    (forall p : Pack@{i i1} A1 A2, B1 (ProjT1@{i i1} p) ≅ B2 (ProjT2@{i i1} p)) ->
  forall (p2 : {x : _ & B2 x}), p1 ≅ p2 -> p1.2 ≅ p2.2) hA _).
  clear A2 hA; intros B2 hB.
  apply heq_to_eq_fam in hB.
  refine (transport@{ij1 ij2} (fun B2 : A1 -> Type@{j} => forall (p2 : {x : A1 & B2 x}), p1 ≅ p2 -> p1.2 ≅ p2.2) hB _).
  clear hB B2; intros p2 hp.
  apply heq_to_eq in hp.
  refine (transport@{ij ij1} (fun p2 => p1.2 ≅ p2.2) hp _).
  apply heq_refl.
Defined.

Lemma cong_eq@{i i1 i2} (A1 A2 : Type@{i})
      (u1 v1 : A1) (u2 v2 : A2)
      (hA : heq@{i1 i2} A1 A2)
  : u1 ≅ u2 -> v1 ≅ v2 -> (u1 = v1) ≅ (u2 = v2).
Proof.
  apply heq_to_eq in hA.
  revert u2 v2.
  refine (transport (fun A2 : Type@{i} => forall u2 v2 : A2, u1 ≅ u2 -> v1 ≅ v2 -> (u1 = v1) ≅ (u2 = v2)) hA _).
  clear A2 hA. intros u2 v2 hu; revert v2.
  apply heq_to_eq in hu.
  refine (transport (fun u2 => forall v2 : A1, v1 ≅ v2 -> (u1 = v1) ≅ (u2 = v2)) hu _).
  intros v2 hv. apply heq_to_eq in hv.
  refine (transport (fun v2 => (u1 = v1) ≅ (u1 = v2)) hv _).
  apply heq_refl.
Defined.

Lemma cong_refl@{i i1 i2} (A1 A2 : Type@{i})
      (u1 : A1) (u2 : A2)
      (hA : heq@{i1 i2} A1 A2)
  : u1 ≅ u2 -> @eq_refl A1 u1 ≅ @eq_refl A2 u2.
Proof.
  apply heq_to_eq in hA.
  revert u2. 
  refine (transport (fun A2 : Type@{i} => forall u2 : A2, u1 ≅ u2 -> @eq_refl A1 u1 ≅ @eq_refl A2 u2) hA _).
  clear A2 hA; intros u2 hu. apply heq_to_eq in hu.
  refine (transport (fun u2 => @eq_refl A1 u1 ≅ @eq_refl A1 u2) hu _).
  apply heq_refl.
Defined.




(* Quote Definition tHeq := @heq. *)
(* Quote Definition tHeqToEq := @heq_to_eq. *)
(* Quote Definition tHeqRefl := @heq_refl. *)
(* Quote Definition tHeqSym := @heq_sym. *)
(* Quote Definition tHeqTrans := @heq_trans. *)
(* Quote Definition tHeqTransport := @heq_transport. *)
(* Quote Definition tPack := @Pack. *)
(* Quote Definition tProjT1 := @ProjT1. *)
(* Quote Definition tProjT2 := @ProjT2. *)
(* Quote Definition tProjTe := @ProjTe. *)
(* Quote Definition tCongProd := @cong_prod. *)
(* Quote Definition tCongLambda := @cong_lambda. *)
(* Quote Definition tCongApp := @cong_app. *)
(* Quote Definition tCongSum := @cong_sum. *)
(* Quote Definition tCongPair := @cong_pair. *)
(* Quote Definition tCongPi1 := @cong_pi1. *)
(* Quote Definition tCongPi2 := @cong_pi2. *)
(* Quote Definition tCongEq := @cong_eq. *)
(* Quote Definition tCongRefl := @cong_refl. *)
(* Quote Definition tEqToHeq := @eq_to_heq. *)
(* Quote Definition tHeqTypeEq := @heq_type_eq. *)

(* Definition mkHeq (A a B b : term) : term := *)
(*   tApp tHeq [ A ; a ; B ; b ]. *)

(* Definition mkHeqToHeq (A u v p : term) : term := *)
(*   tApp tHeqToEq [ A ; u ; v ; p ]. *)

(* Definition mkHeqRefl (A a : term) : term := *)
(*   tApp tHeqRefl [ A ; a ]. *)

(* Definition mkHeqSym (A a B b p : term) : term := *)
(*   tApp tHeqSym [ A ; a ; B ; b ; p ]. *)

(* Definition mkHeqTrans (A a B b C c p q : term) : term := *)
(*   tApp tHeqTrans [ A ; a ; B ; b ; C ; c ; p ; q ]. *)

(* Definition mkHeqTransport (A B p t : term) : term := *)
(*   tApp tHeqTransport [ A ; B ; p ; t ]. *)

(* Definition mkPack (A1 A2 : term) : term := *)
(*   tApp tPack [ A1 ; A2 ]. *)

(* Definition mkProjT1 (A1 A2 p : term) : term := *)
(*   tApp tProjT1 [ A1 ; A2 ; p ]. *)

(* Definition mkProjT2 (A1 A2 p : term) : term := *)
(*   tApp tProjT2 [ A1 ; A2 ; p ]. *)

(* Definition mkProjTe (A1 A2 p : term) : term := *)
(*   tApp tProjTe [ A1 ; A2 ; p ]. *)

(* Definition mkCongProd (A1 A2 B1 B2 pA pB : term) := *)
(*   tApp tCongProd [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) *)
(*   ]. *)

(* Definition mkCongLambda (A1 A2 B1 B2 t1 t2 pA pB pt : term) := *)
(*   tApp tCongLambda [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     (tLambda nAnon A1 t1) ; *)
(*     (tLambda nAnon A2 t2) ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) ; *)
(*     (tLambda nAnon (mkPack A1 A2) pt) *)
(*   ]. *)

(* Definition mkCongApp (A1 A2 B1 B2 t1 t2 u1 u2 pA pB pt pu : term) := *)
(*   tApp tCongApp [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     t1 ; *)
(*     t2 ; *)
(*     u1 ; *)
(*     u2 ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) ; *)
(*     pt ; *)
(*     pu *)
(*   ]. *)

(* Definition mkCongSum (A1 A2 B1 B2 pA pB : term) := *)
(*   tApp tCongSum [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) *)
(*   ]. *)

(* Definition mkCongPair (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv : term) := *)
(*   tApp tCongPair [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     u1 ; *)
(*     u2 ; *)
(*     v1 ; *)
(*     v2 ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) ; *)
(*     pu ; *)
(*     pv *)
(*   ]. *)

(* Definition mkCongPi1 (A1 A2 B1 B2 p1 p2 pA pB pp : term) := *)
(*   tApp tCongPi1 [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     p1 ; *)
(*     p2 ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) ; *)
(*     pp *)
(*   ]. *)

(* Definition mkCongPi2 (A1 A2 B1 B2 p1 p2 pA pB pp : term) := *)
(*   tApp tCongPi2 [ *)
(*     A1 ; *)
(*     A2 ; *)
(*     (tLambda nAnon A1 B1) ; *)
(*     (tLambda nAnon A2 B2) ; *)
(*     p1 ; *)
(*     p2 ; *)
(*     pA ; *)
(*     (tLambda nAnon (mkPack A1 A2) pB) ; *)
(*     pp *)
(*   ]. *)

(* Definition mkCongEq (A1 A2 u1 v1 u2 v2 pA pu pv : term) : term := *)
(*   tApp tCongEq [ A1 ; A2 ; u1 ; v1 ; u2 ; v2 ; pA ; pu ; pv ]. *)

(* Definition mkCongRefl (A1 A2 u1 u2 pA pu : term) : term := *)
(*   tApp tCongRefl [ A1 ; A2 ; u1 ; u2 ; pA ; pu ]. *)

(* Definition mkEqToHeq (A u v p : term) : term := *)
(*   tApp tEqToHeq [ A ; u ; v ; p ]. *)

(* Definition mkHeqTypeEq (A u B v p : term) : term := *)
(*   tApp tHeqTypeEq [ A ; u ; B ; v ; p ]. *)


End Notations.
