
Set Universe Polymorphism.
(* Set Printing Universes. *)

Section Notations.

(** * Pi *)

Axiom Π@{i j} : forall (A : Type@{i}) (B : A -> Type@{j}), Type@{max(i,j)}.
Axiom λ@{i j} : forall {A : Type@{i}} {B : A -> Type@{j}} (t : forall x, B x), Π A B. 
Axiom App@{i j} : forall {A : Type@{i}} (B : A -> Type@{j}) (t : Π A B) (u : A), B u.

Notation "A ⇒ B" := (Π A (fun _ : A => B)) (at level 20, right associativity).
Notation "t $ u" := (App _ t u) (at level 19, left associativity).

(** * Eq *)

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

Axiom β@{i j} : forall {A : Type@{i}} {B : A -> Type@{j}} (t : forall x, B x) (u : A),
    (λ t) $ u = t u.
Axiom funext@{i j ij} : forall {A : Type@{i}} {B : A -> Type@{j}} {f g : Π A B},
    (forall x, f $ x = g $ x) -> eq@{ij} f g.

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x y : A} (p : x = y) (u : P x) : P y
  := J (fun y _ => P y) p u.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

(** * Sigma *)

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

(** * Defined constants *)

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

Definition transportβ@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x} (u : P x)
  : transport@{i j} P 1 u = u
  := Jβ@{i j} (fun x _ => P x)u.

Definition coeβ@{i i1} {A : Type@{i}} (x : A)
  : coe@{i i1} 1 x = x
  := transportβ (fun T => T) x.

Tactic Notation "etransitivity" := refine (_ @ _).
Tactic Notation "transitivity" uconstr(y) := refine (@concat _ _ y _ _ _).
Tactic Notation "symmetry" := refine (_^).
Tactic Notation "reflexivity" := exact 1.


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

Tactic Notation "exists" uconstr(x) := refine (existT _ x _).
Tactic Notation "eexists" := refine (existT _ _ _).


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

Notation "p E@ q" := (heq_trans _ _ _ p q) (at level 20).
Notation "p ^E" := (heq_sym _ _ p) (at level 3, format "p '^E'").
Notation "'E1'" := (heq_refl _).

Tactic Notation "etransitivity" := refine (_ @ _) || refine (_ E@ _).
Tactic Notation "transitivity" uconstr(y) := refine (@concat _ _ y _ _ _) || refine (@heq_trans _ _ _ _ y _ _ _).
Tactic Notation "symmetry" := refine (_^) || refine (_^E).
Tactic Notation "reflexivity" := exact 1 || exact E1.

Tactic Notation "wrevert" ident(H) :=
  revert H;
  match goal with
  | |- (forall x, ?G) => let X := fresh "X" in
                  refine (fun X => App (fun x => G) _ X); clear X
  end.
Tactic Notation "wintro" ident(H) := apply λ; intro H.
Tactic Notation "wdestruct" ident(e) :=
  match type of e with
  | _ = ?y => 
  revert y e;
    match goal with
    | |- (forall y e, ?G) => let X := fresh in let Y := fresh in
                      refine (fun X Y => J (fun y e => G) Y _); clear X Y
    end end.

Tactic Notation "wrevert" ident(H1) ident(H2) := wrevert H1; wrevert H2.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) := wrevert H1; wrevert H2; wrevert H3.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) ident(H4) := wrevert H1; wrevert H2; wrevert H3; wrevert H4.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) := wrevert H1; wrevert H2; wrevert H3; wrevert H4; wrevert H5.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) ident(H6) := wrevert H1; wrevert H2; wrevert H3; wrevert H4; wrevert H5; wrevert H6.
Tactic Notation "wintro" ident(H1) ident(H2) := wintro H1; wintro H2.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) := wintro H1; wintro H2; wintro H3.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) ident(H4) := wintro H1; wintro H2; wintro H3; wintro H4.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) := wintro H1; wintro H2; wintro H3; wintro H4; wintro H5.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) ident(H6) := wintro H1; wintro H2; wintro H3; wintro H4; wintro H5; wintro H6.

Notation "'app' B1" := (fun x => B1 $ x) (at level 12).

Tactic Notation "beta" := refine (β _ _) || refine (β _ _)^.

Tactic Notation "wrevert" ident(H) :=
  revert H;
  match goal with
  | |- (forall x, ?G) => let X := fresh "X" in
                  refine (fun X => App (fun x => G) _ X); clear X
  end.
Tactic Notation "wintro" ident(H) := apply λ; intro H.
Tactic Notation "wdestruct" ident(e) :=
  match type of e with
  | _ = ?y => 
  revert y e;
    match goal with
    | |- (forall y e, ?G) => let X := fresh in let Y := fresh in
                      refine (fun X Y => J (fun y e => G) Y _); clear X Y
    end end.

Tactic Notation "wrevert" ident(H1) ident(H2) := wrevert H1; wrevert H2.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) := wrevert H1; wrevert H2; wrevert H3.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) ident(H4) := wrevert H1; wrevert H2; wrevert H3; wrevert H4.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) := wrevert H1; wrevert H2; wrevert H3; wrevert H4; wrevert H5.
Tactic Notation "wrevert" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) ident(H6) := wrevert H1; wrevert H2; wrevert H3; wrevert H4; wrevert H5; wrevert H6.
Tactic Notation "wintro" ident(H1) ident(H2) := wintro H1; wintro H2.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) := wintro H1; wintro H2; wintro H3.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) ident(H4) := wintro H1; wintro H2; wintro H3; wintro H4.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) := wintro H1; wintro H2; wintro H3; wintro H4; wintro H5.
Tactic Notation "wintro" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) ident(H6) := wintro H1; wintro H2; wintro H3; wintro H4; wintro H5; wintro H6.

Notation "'app' B1" := (fun x => B1 $ x) (at level 12).

Tactic Notation "beta" := refine (β _ _) || refine (β _ _)^.


Definition heq_type_eq@{i i1} {A : Type@{i}} {u : A} {B : Type@{i}} {v : B}
  : heq@{i i1} u v -> A = B
  := projT1.

Lemma heq_transport {A} {B : A -> Type} {x x'} (p : x = x') (t : B x)
  : t ≅ (p # t).
Proof.
  exists (ap B p). wdestruct p. etransitivity.
  apply coeβ'. symmetry; apply transportβ.
Defined.

Lemma heq_coe@{i i1} {T T' : Type@{i}} (p : T = T') (t : T)
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
Definition pack@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: heq @{i i1} x1 x2)
  : Pack@{i i1} A1 A2
  := (x1; (x2; e)).
Definition ProjT1@{i i1} {A1 A2 : Type@{i}} (z : Pack@{i i1} A1 A2) : A1
  := z.1.
Definition ProjT2@{i i1} {A1 A2 : Type@{i}} (z : Pack@{i i1} A1 A2) : A2
  := z.2.1.
Definition ProjTe@{i i1} {A1 A2 : Type@{i}} (z : Pack@{i i1} A1 A2)
  : heq@{i i1} (ProjT1 z) (ProjT2 z)
  := z.2.2.


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

Definition ProjT2β@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: x1 ≅ x2)
 : ProjT2 (pack@{i i1} x1 x2 e) = x2.
Proof.
  unfold ProjT2.
  pose proof ((transport_sigma_const _ _)^
              @ projT2β (fun x1 => exists x2, heq x1 x2) x1 (x2; e)).
  refine (_ @ ap projT1 X @ projT1β _ _ _).
  symmetry; eapply projT1β.
Defined.

(* Definition ProjTeβ@{i i1} {A1 A2 : Type@{i}} (x1 : A1) (x2 : A2) (e: x1 ≅ x2) *)
(*  : ProjTe (pack@{i i1} x1 x2 e) ≅ e. *)



Definition transport_Vp@{i j} {A : Type@{i}} (P : A -> Type@{j})
           {x y} (p : x = y) (u : P x)
  : p^ # (p # u) = u.
Proof.
  wdestruct p. etransitivity. eapply ap. apply transportβ.
  etransitivity. 2: eapply (transportβ P).
  refine (ap (fun p => transport P p u) _). apply K.
Defined.

Definition projT2β'@{i j} {A : Type@{i}} (P : A -> Type@{j}) x (y : P x)
  : (x; y).2 = (projT1β _ _ _)^ # y.
Proof.
  refine (_ @ ap (transport P _) (projT2β P x y)).
  symmetry; apply transport_Vp.
Defined.


Axiom congΠ@{i j j1 ij ij1} : forall {A : Type@{i}}{B B': A -> Type@{j}},
    (forall x, eq@{j1} (B x) (B' x)) -> @eq@{ij1} Type@{ij} (Π@{i j} A B) (Π@{i j} A B').

Lemma congΠβ@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 : Type@{i})
      (B1 B2 : A1 -> Type@{j}) (f1 : Π A1 B1)
      (hB : forall x, B1 x = B2 x)
  : coe@{ij ij1} (congΠ@{i j j1 ij ij1} hB) f1
    = λ@{i j} (fun x => coe (hB x) (f1 $ x)).
Proof.
Admitted.


Lemma cong_prod@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : @heq@{ij1 ij2} Type@{ij} (Π A1 B1) Type@{ij} (Π A2 B2).
Proof.
  apply heq_to_eq in hA. apply eq_to_heq.
  pose (B2' := λ@{i j1} B2).
  refine (@concat Type@{ij} _ (Π@{i j} A2 (app B2')) _ _ _).
  2: apply congΠ@{i j j1 ij ij1}; intro x; apply (β@{i j1} B2 x).
  assert (XX: Π@{ij1 ij1} _ (fun B2' => (Π@{ij1 ij1} (Pack@{i i1} A1 A2) (fun p => B1 (ProjT1@{i i1} p) ≅ B2' $ (ProjT2@{i i1} p))) ⇒ (@eq Type@{ij} (Π@{i j} A1 B1) (Π@{i j} A2 (fun x => B2' $ x))))). {
    refine (transport (fun A2 => Π@{ij1 ij1} (A2 ⇒ Type@{j}) (fun B2' : A2 ⇒ Type@{j} => Π@{ij1 ij1} (Pack@{i i1} A1 A2) (fun p : Pack@{i i1} A1 A2 => B1 (ProjT1@{i i1} p) ≅ B2' $ ProjT2@{i i1} p) ⇒ (@eq Type@{ij} (Π@{i j} A1 B1) (Π@{i j} A2 (fun x : A2 => B2' $ x)))) ) hA _).
    clear. apply λ; intro B2'.
    apply λ; intro p.
    eapply congΠ@{i j j1 ij ij1}.
    intro x. pose proof (p $ (pack@{i i1} x x (heq_refl x))).
    cbn in *. apply heq_to_eq in X. etransitivity. etransitivity.
    2: exact X. all: apply ap.
    symmetry. apply ProjT1β. apply ProjT2β. }
  refine (XX $ _ $ _). clear XX. eapply λ; intro p.
  eapply heq_trans. eapply hB. eapply eq_to_heq.
  symmetry. unfold B2'. eapply (β@{i j1} B2).
Defined.


Definition congΠ'@{i i1 j j1 ij ij1} {A1 A2: Type@{i}}
           {B1 : A1 -> Type@{j}}{B2 : A2 -> Type@{j}}
           (pA : A1 = A2)
           (pB : forall x, eq@{j1} (B1 x) (B2 (coe@{i i1} pA x)))
  : @eq@{ij1} Type@{ij} (Π@{i j} A1 B1) (Π@{i j} A2 B2).
Proof.
  pose (B2' := λ B2).
  refine (@concat Type@{ij} _ (Π@{i j} A1 (fun x => B2' $ (coe@{i i1} pA x))) _ _ _).
  2:refine (@concat Type@{ij} _ (Π@{i j} A2 (fun x => B2' $ x)) _ _ _).
  - apply congΠ. intro x.
    etransitivity. eapply pB. symmetry.
    eapply (β@{i j1} B2).
  - clearbody B2'; clear.
    assert (Π@{ij1 ij1} (A2 ⇒ Type@{j}) (fun B2' => @eq Type@{ij} (Π@{i j} A1 (fun x : A1 => B2' $ coe@{i i1} pA x)) (Π@{i j} A2 (fun x : A2 => B2' $ x)))). {
      clear B2'.
      refine (J (fun A2 pA => Π@{ij1 ij1} (A2 ⇒ Type@{j}) (fun B2' : A2 ⇒ Type@{j} => @eq Type@{ij} (Π@{i j} A1 (fun x : A1 => B2' $ coe@{i i1} pA x)) (Π@{i j} A2 (fun x : A2 => B2' $ x)))) pA _).
      apply λ; intro B. eapply congΠ.
      intro x. refine (ap (fun x => B $ x) _). apply coeβ. }
    refine (X $ _).
  - apply congΠ. eapply (β@{i j1} B2).
Defined.


Definition coe_pV@{i i1} {A B : Type@{i}} (p : A = B) x
  : coe p (coe@{i i1} p^ x) = x.
Proof.
  wrevert x. wdestruct p.
  wintro x. etransitivity. eapply coeβ. eapply coeβ'.
Defined.


(* Lemma coeΠ00@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 : Type@{i}) *)
(*       (B1 B2 : A1 ⇒ Type@{j}) (f1 : Π A1 (app B1)) *)
(*       (hB : Π A1 (fun x => B1 $ x = B2 $ x)) *)
(*   : coe@{ij ij1} (congΠ@{i j j1 ij ij1} (fun x => hB $ x)) f1 *)
(*     = λ@{i j} (fun x => coe (hB $ x) (f1 $ x)). *)
(* Proof. *)
(*   assert (hB': B1 = B2). { *)
(*     apply funext. intro x. exact (hB $ x). } *)
(*   simple refine (let hB'' := _ : Π@{i j1} A1 (fun x : A1 => B1 $ x = B2 $ x) in _). { *)
(*     wintro x. exact (ap (fun B2 => B2 $ x) hB'). } *)
(*   assert (coe@{ij ij1} (congΠ@{i j j1 ij ij1} (fun x : A1 => hB'' $ x)) f1 = λ@{i j} (fun x : A1 => coe@{j j1} (hB'' $ x) (f1 $ x))). { *)
(*     clear hB; subst hB''. *)
(*   revert B2 hB'; *)
(*     match goal with *)
(*     | |- (forall x y, ?G) => refine (fun X Y => J (fun x y => G) Y _); clear X Y *)
(*     end. *)
(*   etransitivity. eapply coeβ'. *)
(*   eapply funext; intro x. *)
(*   symmetry. etransitivity. eapply β. *)
(*   eapply coeβ'. } *)
(* Admitted. *)



(* Lemma coeΠ0@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A1 ⇒ Type@{j}) (f1 : Π A1 B1) *)
(*       (hB : Π A1 (fun x => B1 x = B2 $ x)) *)
(*   : coe@{ij ij1} (congΠ@{i j j1 ij ij1} (fun x => hB $ x)) f1 *)
(*     = λ@{i j} (fun x => coe (hB $ x) (f1 $ x)). *)
(* Proof. *)
(*   simple refine (let XX :=  coeΠ00 A1 (λ B1) B2 _ _ in _). *)
(*   - wintro x. refine (coe _ (f1 $ x)). symmetry. refine (β _ _). *)
(*   - wintro x. etransitivity. 2: exact (hB $ x). refine (β _ _). *)
(*   - clearbody XX. *)
(* Abort. *)

  (* assert (hB': λ B1 = B2). { *)
  (*   apply funext. intro x. etransitivity. eapply (β B1). *)
  (*   exact (hB $ x). } *)
  (* simple refine (let hB'' := _ : Π@{i j1} A1 (fun x : A1 => B1 x = B2 $ x) in _). { *)
  (*   wintro x. etransitivity. 2: exact (ap (fun B2 => B2 $ x) hB'). *)
  (*   symmetry; apply (β B1). } *)
  (* assert (coe@{ij ij1} (congΠ@{i j j1 ij ij1} (fun x : A1 => hB'' $ x)) f1 = λ@{i j} (fun x : A1 => coe@{j j1} (hB'' $ x) (f1 $ x))). { *)
  (*   clear hB; subst hB''. *)
  (* revert B2 hB'; *)
  (*   match goal with *)
  (*   | |- (forall x y, ?G) => refine (fun X Y => J (fun x y => G) Y _); clear X Y *)
  (*   end. *)

  (* match goal with *)
  (* | |- coe ?XX _ = _ => set XX *)
  (* end. *)



(* Lemma coeΠ0@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 ⇒ Type@{j}) (f1 : Π A1 B1) *)
(*       (hA : A1 = A2) (hB : Π A1 (fun x => B1 x = B2 $ (coe@{i i1} hA x))) *)
(*   : coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} hA (fun x => hB $ x)) f1 *)
(*     = λ@{i j} (fun x => coe@{j j1} (hB $ (coe@{i i1} hA^ x) *)
(*                @ ap@{i j1} (fun x => B2 $ x) (coe_pV@{i i1} hA x)) (f1 $ coe@{i i1} hA^ x)). *)
(* Proof. *)
(*   wrevert hB. *)
(*   wrevert B2. *)
(*   wdestruct A2 hA. *)
(*   wintro B2. wintro hB. *)
(*   assert (hB': λ B1 = B2). { *)
(*     apply funext. intro x. etransitivity. eapply (β B1). *)
(*     etransitivity. exact (hB $ x). *)
(*     refine (ap (fun x => B2 $ x) _). apply coeβ. } *)
(*   simple refine (let hB'' := _ : Π@{i j1} A1 (fun x : A1 => B1 x = B2 $ coe@{i i1} 1 x) *)
(*                  in _). { *)
(*     wintro x. etransitivity. *)
(*     2: exact (ap (fun f => f $ _) hB'). symmetry. etransitivity. *)
(*     eapply (β B1). eapply ap, coeβ. } *)
(*   assert (coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} 1 (fun x : A1 => hB'' $ x)) f1 = λ@{i j} (fun x : A1 => coe@{j j1} (hB'' $ coe@{i i1} 1^ x @ ap@{i j1} (fun x0 : A1 => B2 $ x0) (coe_pV@{i i1} 1 x)) (f1 $ coe@{i i1} 1^ x))). { *)
(*     clear hB. subst hB''. *)
(*   revert B2 hB'; *)
(*     match goal with *)
(*     | |- (forall x y, ?G) => refine (fun X Y => J (fun x y => G) Y _); clear X Y *)
(*     end. *)
  
(*   match goal with *)
(*   | |- coe ?XX _ = _ => set XX *)
(*   end. *)
(* Abort. *)




(* Lemma coeΠ@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j}) *)
(*       (f1 : Π A1 B1) (f2 : Π A2 B2) *)
(*       (hA : A1 = A2) (hB : forall x : A1, B1 x = B2 (coe@{i i1} hA x)) *)
(*       (hB' : forall x, B1 (coe@{i i1} hA^ x) = B2 x := fun x => hB _ @ ap B2 (coe_pV hA x)) *)
(*   : coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} hA hB) f1 *)
(*     = λ (fun x => coe (hB' x) (f1 $ (coe hA^ x))). *)
(* Proof. *)
(*   subst hB'. cbn. *)
(*   pose (hB' := λ@{j1 ij1} hB). *)
(*   transitivity (coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} hA (fun x => hB' $ x)) f1). *)
(*   admit. *)
(*   clearbody hB'; clear. *)

  (* refine (@App@{ij1 ij1} _ (fun hB' => coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} 
hA (fun x : A1 => hB' $ x)) f1 = f2) _ hB'). clear. *)
  (* refine (@App@{ij1 ij1} _ (fun f2 =>  Π@{ij1 ij1} (Π@{j1 ij1} A1 (fun x : A1 => B1 x = B2 (coe@{i i1} hA x))) (fun hB' : Π@{j1 ij1} A1 (fun x : A1 => B1 x = B2 (coe@{i i1} hA x)) => coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} hA (fun x : A1 => hB' $ x)) f1 = f2)) *)
  (*             _ f2). clear. *)
  (* refine (@App@{ij1 ij1} _ (fun B2 => Π@{ij1 ij1} (Π@{i j} A2 B2) (fun f2 : Π@{i j} A2 B2 => Π@{ij1 ij1} (Π@{j1 ij1} A1 (fun x : A1 => B1 x = B2 (coe@{i i1} hA x))) (fun hB' : Π@{j1 ij1} A1 (fun x : A1 => B1 x = B2 (coe@{i i1} hA x)) => coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} hA (fun x : A1 => hB' $ x)) f1 = f2))) _ B2) *)

(*   refine (J (fun A2 hA =>  Π@{ij1 ij1} (Π@{j1 ij1} A1 (fun x : A1 => B1 x = B2 (coe@{i i1} hA x))) (fun hB'0 : Π@{j1 ij1} A1 (fun x : A1 => B1 x = B2 (coe@{i i1} hA x)) => coe@{ij ij1} (congΠ'@{i i1 j j1 ij ij1} hA (fun x : A1 => hB'0 $ x)) f1 = f2)) hA _). *)
(* )) *)

Lemma heq_fam_to_eq (A1 : Type) (B1 B2 : A1 ⇒ Type)
      (hB : Π (Pack A1 A1) (fun p => B1 $ ProjT1 p ≅ B2 $ ProjT2 p))
  : B1 = B2.
Proof.
  apply funext; intro x.
  refine (_ @ heq_to_eq (hB $ (pack x x E1)) @ _).
  refine (ap (fun x => B1 $ x) _). symmetry; apply ProjT1β.
  refine (ap (fun x => B2 $ x) _). apply ProjT2β.
Defined.
    


(* Lemma cong_lambda0@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 ⇒ Type@{j}) (B2 : A2 ⇒ Type@{j}) *)
(*       (f1 : Π A1 (fun x => B1 $ x)) (f2 : Π A2 (fun x => B2 $ x)) *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : Π (Pack@{i i1} A1 A2) (fun p => heq@{j1 j2} (B1 $ (ProjT1 p)) (B2 $ (ProjT2 p)))) *)
(*       (hf : Π (Pack@{i i1} A1 A2) (fun p => f1 $ (ProjT1 p) ≅ f2 $ (ProjT2 p))) *)
(*   : heq@{ij ij1} f1 f2. *)
Lemma cong_lambda0 (A1 A2 : Type)
      (B1 : A1 ⇒ Type) (B2 : A2 ⇒ Type)
      (f1 : Π A1 (fun x => B1 $ x)) (f2 : Π A2 (fun x => B2 $ x))
      (hA : heq A1 A2)
      (hB : Π (Pack A1 A2) (fun p => heq (B1 $ (ProjT1 p)) (B2 $ (ProjT2 p))))
      (hf : Π (Pack A1 A2) (fun p => f1 $ (ProjT1 p) ≅ f2 $ (ProjT2 p)))
  : heq f1 f2.
Proof.
  apply heq_to_eq in hA.
  wrevert hf f2 hB B2. wdestruct hA. wintro B2 hB.
  apply heq_fam_to_eq in hB. wdestruct hB.
  wintro f2 hf. apply eq_to_heq, funext; intro x.
  apply heq_to_eq.
  refine (_ E@ (hf $ (pack x x E1)) E@ _).
  unshelve eexists. exact (ap (fun x => B1 $ x) (ProjT1β _ _ _)^).
  (* set (ProjT1β@{i i1} x x E1)^. *)
  (* set (y := ProjT1@{i i1} (pack@{i i1} x x E1)) in *. *)
  (* clearbody e y. wdestruct y e. apply coeβ'. *)
  (* set (ProjT2β@{i i1} x x E1)^. *)
  (* set (y := ProjT2@{i i1} (pack@{i i1} x x E1)) in *. *)
  set (ProjT1β x x E1)^.
  set (y := ProjT1 (pack x x E1)) in *.
  clearbody e y. wdestruct e. apply coeβ'.
  set (ProjT2β x x E1)^.
  set (y := ProjT2 (pack x x E1)) in *.
  clearbody e y. wdestruct e. exact E1.
Defined.


(* Lemma cong_lambda@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j}) *)
(*       (f1 : forall x, B1 x) (f2 : forall x, B2 x) *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p))) *)
(*       (hf : forall (p : Pack@{i i1} A1 A2), f1 (ProjT1 p) ≅ f2 (ProjT2 p)) *)
(*   : heq@{ij ij1} (λ f1) (λ f2). *)
Lemma cong_lambda (A1 A2 : Type)
      (B1 : A1 -> Type) (B2 : A2 -> Type)
      (f1 : forall x, B1 x) (f2 : forall x, B2 x)
      (hA : heq A1 A2)
      (hB : forall (p : Pack A1 A2), heq (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hf : forall (p : Pack A1 A2), f1 (ProjT1 p) ≅ f2 (ProjT2 p))
  : heq (λ f1) (λ f2).
Proof.
  simple refine (let XX := cong_lambda0 A1 A2 (λ B1) (λ B2) (λ (fun x => coe (β B1 x)^ (f1 x))) (λ (fun x => coe (β B2 x)^ (f2 x))) hA _ (* hB *) _ (* hf *) in _).
  - wintro p. refine (_ E@ hB p E@ _).
    all: eapply eq_to_heq; beta.
  - wintro p. refine (_ E@ hf p E@ _).
    unshelve eexists. beta.
    refine (ap (coe _) _ @ _). beta. apply coe_pV.
    unshelve eexists. beta.
    etransitivity. 2: refine (β _ _)^. reflexivity.
  - refine (_ E@ XX E@ _); clear. 
    + apply heq_sym. unshelve eexists.
      apply congΠ. intro x; refine (β _ _).
      etransitivity. eapply congΠβ. cbn.
      apply funext; intro x. refine (β _ _ @ _ @ (β _ _)^).
      refine (ap (coe _) _ @ _). refine (β _ _). apply coe_pV.
    + apply heq_sym. unshelve eexists.
      apply congΠ. intro x; refine (β _ _)^.
      etransitivity. eapply congΠβ. cbn.
      apply funext; intro x. refine (β _ _ @ _ @ (β _ _)^).
      refine (ap (coe _) _). refine (β _ _).
Defined.

Lemma cong_app0 (A1 A2 : Type)
      (B1 : A1 ⇒ Type) (B2 : A2 ⇒ Type)
      (f1 : Π A1 (app B1)) (f2 : Π A2 (app B2))
      (u1 : A1) (u2 : A2)
      (hA : heq A1 A2)
      (hB : Π (Pack A1 A2) (fun p => heq (B1 $ (ProjT1 p)) (B2 $ (ProjT2 p))))
      (hf : heq f1 f2)
      (hu : u1 ≅ u2)
  : f1 $ u1 ≅ f2 $ u2.
Proof.
  wrevert hu u2 hf f2 hB B2.
    apply heq_to_eq in hA. wdestruct hA. wintro B2 hB.
  apply heq_fam_to_eq in hB. wdestruct hB.
  wintro f2 hf. apply heq_to_eq in hf. wdestruct hf.
  wintro u2 hu. apply heq_to_eq in hu. wdestruct hu.
  exact E1.
Defined.

(* Lemma cong_app@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j}) *)
(*       (f1 : Π A1 B1) (f2 : Π A2 B2) *)
(*       (u1 : A1) (u2 : A2) *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p))) *)
(*       (hf : heq@{ij ij1} f1 f2) *)
(*       (hu : u1 ≅ u2) *)
(*   : f1 $ u1 ≅ f2 $ u2. *)
Lemma cong_app (A1 A2 : Type)
      (B1 : A1 -> Type) (B2 : A2 -> Type)
      (f1 : Π A1 B1) (f2 : Π A2 B2)
      (u1 : A1) (u2 : A2)
      (hA : heq A1 A2)
      (hB : forall (p : Pack A1 A2), heq (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hf : heq f1 f2)
      (hu : u1 ≅ u2)
  : f1 $ u1 ≅ f2 $ u2.
Proof.
  simple refine (let XX := cong_app0 A1 A2 (λ B1) (λ B2) _ _ u1 u2 hA _ (* hB *) _ (* hf *) hu in _).
  - refine (λ (fun x => coe (β B1 x)^ (f1 $ x))).
  - refine (λ (fun x => coe (β B2 x)^ (f2 $ x))).
  - wintro p. refine (_ E@ hB p E@ _).
    eapply eq_to_heq. refine (β _ _).
    eapply eq_to_heq. refine (β _ _)^.
  - refine (_ E@ hf E@ _).
    unshelve eexists. apply congΠ. intro; refine (β _ _).
    etransitivity. apply congΠβ. apply funext; intro x.
    refine (β _ _ @ _). refine (ap (coe _) _ @ _).
    refine (β _ _). apply coe_pV.
    unshelve eexists. apply congΠ. intro; refine (β _ _)^.
    etransitivity. apply congΠβ. reflexivity.
  - refine (_ E@ XX E@ _); clear XX.
    + eapply heq_trans. 2: apply eq_to_heq; refine (β _ _)^.
      apply heq_coe.
    + eapply heq_trans. apply eq_to_heq; refine (β _ _).
      apply heq_sym, heq_coe.
Defined.


Axiom congΣ@{i j j1 ij ij1} : forall {A : Type@{i}}{B B': A -> Type@{j}},
    (forall x, eq@{j1} (B x) (B' x)) -> @eq@{ij1} Type@{ij} (sigT@{i j} B) (sigT@{i j} B').

Lemma congΣβ@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 : Type@{i})
      (B1 B2 : A1 -> Type@{j}) u v
      (hB : forall x, B1 x = B2 x)
  : coe@{ij ij1} (congΣ@{i j j1 ij ij1} hB) (u; v)
    = (u; coe (hB _) v).
Proof.
Admitted.

Lemma cong_sum@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i})
      (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j})
      (hA : heq@{i1 i2} A1 A2)
      (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p)))
  : @heq@{ij1 ij2} Type@{ij} (sigT B1) Type@{ij} (sigT B2).
Proof.
  apply heq_to_eq in hA. apply eq_to_heq.
  pose (B2' := λ@{i j1} B2).
  refine (@concat Type@{ij} _ (sigT@{i j} (app B2')) _ _ _).
  2: apply congΣ@{i j j1 ij ij1}; intro x; apply (β@{i j1} B2 x).
  assert (hB': (Π@{ij1 ij1} (Pack@{i i1} A1 A2) (fun p => B1 (ProjT1@{i i1} p) ≅ B2' $ (ProjT2@{i i1} p)))). {
    wintro p. refine (hB p E@ _). apply eq_to_heq.
    refine (β _ _)^. }
  clearbody B2'; clear B2 hB. wrevert hB'. wrevert B2'.
  let e := hA in
  match type of e with
  | _ = ?y => 
  revert y e;
    match goal with
    | |- (forall y e, ?G) => let X := fresh in let Y := fresh in
                      refine (fun X Y => J@{i1 ij1} (fun y e => G) Y _); clear X Y
    end end.
  refine (λ@{i ij1} (fun B2 => _)). wintro hB. apply congΣ.
  intro x. pose proof (hB $ (pack@{i i1} x x (heq_refl x))).
  cbn in *. apply heq_to_eq in X. etransitivity. etransitivity.
  2: exact X. all: apply ap.
  symmetry. apply ProjT1β. apply ProjT2β.
Defined.

Lemma cong_pair0 (A1 A2 : Type)
      (B1 : A1 ⇒ Type) (B2 : A2 ⇒ Type)
      (u1 : A1) (u2 : A2) (v1 : B1 $ u1) (v2 : B2 $ u2)
      (hA : heq A1 A2)
      (hB : Π (Pack A1 A2) (fun p => heq (B1 $ (ProjT1 p)) (B2 $ (ProjT2 p))))
      (hu : u1 ≅ u2) (hv : v1 ≅ v2)
  : (existT _ u1 v1) ≅ (existT _ u2 v2).
Proof.
  wrevert hv v2 hu u2 hB B2.
  apply heq_to_eq in hA. wdestruct hA. wintro B2 hB.
  apply heq_fam_to_eq in hB. wdestruct hB.
  wintro u2 hu. apply heq_to_eq in hu; wdestruct hu.
  wintro v2 hv. apply heq_to_eq in hv; wdestruct hv.
  exact E1.
Defined.

Lemma eq_sigma {A} (B : A -> Type) {x x' : A} {y : B x} {y' : B x'}
      (e1 : x = x') (e2 : e1 # y = y')
  : (x; y) = (x'; y').
Proof.
  wrevert e2 y'. wdestruct e1.
  wintro y' e2. pose proof ((transportβ B y)^ @ e2).
  clear e2. wdestruct X. reflexivity.
Defined.

(* Lemma cong_pair@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j}) *)
(*       (u1 : A1) (u2 : A2) (v1 : B1 u1) (v2 : B2 u2) *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p))) *)
(*       (hu : u1 ≅ u2) (hv : v1 ≅ v2) *)
(*   : heq@{ij ij1} (existT B1 u1 v1) (existT B2 u2 v2). *)
Lemma cong_pair (A1 A2 : Type)
      (B1 : A1 -> Type) (B2 : A2 -> Type)
      (u1 : A1) (u2 : A2) (v1 : B1 u1) (v2 : B2 u2)
      (hA : heq A1 A2)
      (hB : forall (p : Pack A1 A2), heq (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hu : u1 ≅ u2) (hv : v1 ≅ v2)
  : heq (existT B1 u1 v1) (existT B2 u2 v2).
Proof.
  simple refine (let XX := cong_pair0 A1 A2 (λ B1) (λ B2) u1 u2 (coe (β _ _)^ v1) (coe (β _ _)^ v2) hA _ hu _ in _ E@ XX E@ _).
  - wintro p. refine (eq_to_heq (β _ _) E@ _ E@ eq_to_heq (β _ _)^).
    apply hB.
  - refine (_^E E@ hv E@ _); apply heq_coe; clear.
  - unshelve eexists. apply congΣ. intro x; refine (β _ _)^.
    etransitivity. apply congΣβ. reflexivity. 
  - eapply heq_sym. unshelve eexists. apply congΣ. intro x; refine (β _ _)^.
    etransitivity. apply congΣβ. reflexivity. 
Defined.

Lemma cong_pi10 (A1 A2 : Type) (B1 : A1 ⇒ Type) (B2 : A2 ⇒ Type)
      (p1 : sigT (app B1)) (p2 : sigT (app B2))
      (hA : heq A1 A2)
      (hB : Π (Pack A1 A2) (fun p => heq (B1 $ (ProjT1 p)) (B2 $ (ProjT2 p))))
      (hp : p1 ≅ p2)
  : p1.1 ≅ p2.1.
Proof.
  wrevert hp p2 hB B2.
  apply heq_to_eq in hA. wdestruct hA. wintro B2 hB.
  apply heq_fam_to_eq in hB. wdestruct hB.
  wintro p2 hp. apply heq_to_eq in hp; wdestruct hp.
  exact E1.
Defined.

(* Lemma cong_pi1@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j}) *)
(*       (p1 : sigT B1) (p2 : sigT B2) *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p))) *)
(*       (hp : heq@{ij ij1} p1 p2) *)
(*   : p1.1 ≅ p2.1. *)
Lemma cong_pi1 (A1 A2 : Type)
      (B1 : A1 -> Type) (B2 : A2 -> Type)
      (p1 : sigT B1) (p2 : sigT B2)
      (hA : heq A1 A2)
      (hB : forall (p : Pack A1 A2), heq (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hp : p1 ≅ p2)
  : p1.1 ≅ p2.1.
Proof.
  simple refine (let XX := cong_pi10 A1 A2 (λ B1) (λ B2) _ _ hA _ _ in _ E@ XX E@ _).
  - refine (coe _ p1). apply congΣ. intro; beta.
  - refine (coe _ p2). apply congΣ. intro; beta.
  - wintro p. refine (_ E@ hB p E@ _); apply eq_to_heq.
    refine (β _ _). refine (β _ _)^.
  - refine (_^E E@ hp E@ _); apply heq_coe.
  - clear. apply eq_to_heq. symmetry. etransitivity.
    eapply ap. etransitivity. apply ap. 2: apply congΣβ.
    symmetry; apply Ση. apply projT1β.
  - clear. apply eq_to_heq. etransitivity.
    eapply ap. etransitivity. apply ap. 2: apply congΣβ.
    symmetry; apply Ση. apply projT1β.
Defined.


Lemma cong_pi20 (A1 A2 : Type) (B1 : A1 ⇒ Type) (B2 : A2 ⇒ Type)
      (p1 : sigT (app B1)) (p2 : sigT (app B2))
      (hA : heq A1 A2)
      (hB : Π (Pack A1 A2) (fun p => heq (B1 $ (ProjT1 p)) (B2 $ (ProjT2 p))))
      (hp : p1 ≅ p2)
  : p1.2 ≅ p2.2.
Proof.
  wrevert hp p2 hB B2.
  apply heq_to_eq in hA. wdestruct hA. wintro B2 hB.
  apply heq_fam_to_eq in hB. wdestruct hB.
  wintro p2 hp. apply heq_to_eq in hp; wdestruct hp.
  exact E1.
Defined.

Definition Eap {A} {B : A -> Type} (f : forall x, B x) {x x'} (e : x = x')
  : f x ≅ f x'.
Admitted.


(* Lemma cong_pi2@{i i1 i2 j j1 j2 ij ij1 ij2} (A1 A2 : Type@{i}) *)
(*       (B1 : A1 -> Type@{j}) (B2 : A2 -> Type@{j}) *)
(*       (p1 : sigT B1) (p2 : sigT B2) *)
(*       (hA : heq@{i1 i2} A1 A2) *)
(*       (hB : forall (p : Pack@{i i1} A1 A2), heq@{j1 j2} (B1 (ProjT1 p)) (B2 (ProjT2 p))) *)
(*   : heq@{ij ij1} p1 p2 -> p1.2 ≅ p2.2. *)
Lemma cong_pi2 (A1 A2 : Type)
      (B1 : A1 -> Type) (B2 : A2 -> Type)
      (p1 : sigT B1) (p2 : sigT B2)
      (hA : heq A1 A2)
      (hB : forall (p : Pack A1 A2), heq (B1 (ProjT1 p)) (B2 (ProjT2 p)))
      (hp : p1 ≅ p2)
  : p1.2 ≅ p2.2.
Proof.
  simple refine (let XX := cong_pi20 A1 A2 (λ B1) (λ B2) _ _ hA _ _ in _ E@ XX E@ _).
  - refine (coe _ p1). apply congΣ. intro; beta.
  - refine (coe _ p2). apply congΣ. intro; beta.
  - wintro p. refine (_ E@ hB p E@ _); apply eq_to_heq.
    refine (β _ _). refine (β _ _)^.
  - refine (_^E E@ hp E@ _); apply heq_coe.
  - clear. symmetry.
    pose proof (Ση _ p1). set (p1' := (p1.1; p1.2)) in *.
    transitivity (coe (congΣ (fun x : A1 => (β B1 x)^)) p1').2.
    clearbody p1'. wdestruct X. reflexivity.
    subst p1'; clear X.
    pose proof (congΣβ _ _ _ p1.1 p1.2 (fun x => (β B1 x)^))^.
    set (Y := coe (congΣ (fun x : A1 => (β B1 x)^)) (p1.1; p1.2)) in *.
    etransitivity. clearbody Y. wdestruct X. reflexivity.
    etransitivity. apply eq_to_heq. eapply projT2β'.
    symmetry. etransitivity. 2: eapply heq_transport.
    eapply heq_coe.
  - clear. pose proof (Ση _ p2). set (p2' := (p2.1; p2.2)) in *.
    transitivity (coe (congΣ (fun x : A2 => (β B2 x)^)) p2').2.
    clearbody p2'. wdestruct X. reflexivity.
    subst p2'; clear X.
    pose proof (congΣβ _ _ _ p2.1 p2.2 (fun x => (β B2 x)^))^.
    set (Y := coe (congΣ (fun x : A2 => (β B2 x)^)) (p2.1; p2.2)) in *.
    etransitivity. clearbody Y. wdestruct X. reflexivity.
    etransitivity. apply eq_to_heq. eapply projT2β'.
    symmetry. etransitivity. 2: eapply heq_transport.
    eapply heq_coe.
Defined.


Lemma cong_eq@{i i1 i2} (A1 A2 : Type@{i})
      (u1 v1 : A1) (u2 v2 : A2)
      (hA : heq@{i1 i2} A1 A2)
      (hu : u1 ≅ u2) (hv :  v1 ≅ v2)
  : (u1 = v1) ≅ (u2 = v2).
Proof.
  apply heq_to_eq in hA.
  wrevert hv v2 hu u2. wdestruct hA.
  wintro u2 hu; apply heq_to_eq in hu; wdestruct hu.
  wintro v2 hv; apply heq_to_eq in hv; wdestruct hv.
  reflexivity.
Defined.

Lemma cong_refl@{i i1 i2} (A1 A2 : Type@{i})
      (u1 : A1) (u2 : A2)
      (hA : heq@{i1 i2} A1 A2) (hu : u1 ≅ u2)
  : @eq_refl A1 u1 ≅ @eq_refl A2 u2.
Proof.
  apply heq_to_eq in hA.
  wrevert hu u2. wdestruct hA.
  wintro u2 hu; apply heq_to_eq in hu; wdestruct hu.
  reflexivity.
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
