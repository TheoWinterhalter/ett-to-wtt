# Eliminating Reflection from Type Theory
**A translation from extensional type theory (ETT) to weak type theory (WTT)**

*Authors:* Théo Winterhalter and Simon Boulier

Based on previous work with Matthieu Sozeau and Nicolas Tabareau:
[ett-to-itt]. This repository is in fact more or less a fork of the other one.

[ett-to-itt]: https://github.com/TheoWinterhalter/ett-to-itt

**Quick jump**
- [Installing](#installing)
- [Structure](#structure-of-the-project)

## Overview

This work is a Coq formalisation of a translation from ETT to WTT.
Additionally, sorts are handled quite generically (although without
cumulativity) which means in particular that we can have a translation from
Homotopy Type System (HTS) to Two-Level Weak Type Theory (2WTT) as a direct
application.

ETT differs from ITT by the addition of the **reflection rule**:
```
Γ ⊢ e : u = v
--------------
  Γ ⊢ u ≡ v
```

WTT is ITT without any notion of computation or conversion, operations like
β-reduction are instead handled directly with propositional equalities.

## Installing

### Requirements

This project can be compiled with Coq 8.16 and requires
[Equations](http://mattam82.github.io/Coq-Equations/) 1.3.

You can install those via opam with
```fish
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-equations.1.3+8.16
```

### Building

Once you have the dependencies, simply run
```bash
make
```
to build the project (it takes quite some time unfortunately, so you
can use options like `-j4` to speed up a little bit).


## Structure of the project

All of the formalisation can be found in the `theories` directory.

*The file [util.v](theories/util.v)
provides useful lemmata that aren't specific to the formalisation.*

### Syntax

First, [Sorts](theories/Sorts.v) introduces a notion of sort (as a type-class)
stating the basic properties required, and provides different instances
like the natural number hierarchy, type-in-type, or even HTS/2-level TT.
In [SAst](SAst.v) we define the common syntax to both ETT (Extensional type
theory) and WTT in the form of a simple inductive type `sterm`.
Since terms (`sterm`) are annotated with names—for printing—which are
irrelevant for computation and typing, we define an erasure map
`nl : sterm -> nlterm` in [Equality](theories/Equality.v) from which we derive
a decidable equality on `sterm`.
We then define lifting operations, substitution and closedness in
[SLiftSubst](SLiftSubst.v).

### Typing

First, in [SCommon](theories/SCommon.v) we define common utility to both ETT and
WTT, namely with the definition of contexts (`scontext`) and global
contexts (`sglobal_context`), the latter containing the declarations of
constants.
[XTyping](theories/XTyping.v) contains the definition of typing rules of ETT
(`Σ ;;; Γ |-x t : A`), mutually defined with a typed conversion
(`Σ ;;; Γ |-x t ≡ u : A`) and the well-formedness of contexts (`wf Σ Γ`).
[ITyping](theories/ITyping.v) is the same for WTT with the difference that there
is no notion of conversion, and that it also defines a notion of
well-formedness of global declarations (`type_glob Σ`).

### Lemmata regarding WTT

In [ITypingInversions](theories/ITypingInversions.v) one can find an inversion
lemma for each constructor of the syntax, together with the tactic `ttinv` to
apply the right one.
In [ITypingLemmata](theories/ITypingLemmata.v) are proven a list of different
lemmata regarding WTT, including the fact that whenever we have
`Σ ;;; Γ |-i t : A` then `A` is well sorted and that lifting and substitution
preserve typing.
A uniqueness of typing lemma for WTT (if `Σ ;;; Γ |-i t :A` and
`Σ ;;; Γ |-i t :B` then `A` and `B` are α-equivalent) is proven in
[Uniqueness](theories/Uniqueness.v).
[ITypingAdmissible](theories/ITypingAdmissible.v) states admissible rules in
ITT.

### Translation

[PackLifts](PackLifts.v) defines the lifting operations related to packing.
Packing consists in taking two types `A1` and `A2` and yielding the following
record type (where `x ≅ y` stands for heterogenous equality between `x` and
`y`).
```coq
Record Pack A1 A2 := pack {
  ProjT1 : A1 ;
  ProjT2 : A2 ;
  ProjTe : ProjT1 ≅ ProjT2
}.
```
In order to produce terms as small / efficient as possible, we provide
*optimised* versions of some constructors, for instance, transport
between two convertible terms is remapped to identity. Thanks to this, terms
that live in WTT should be translated to themselves syntactically (and not just
up to transport).
This is done in [Optim](theories/Optim.v).
[FundamentalLemma](theories/FundamentalLemma.v) contains the proof of the
fundamental lemma, crucial step for our translation.
[Translation](theories/Translation.v) contains the translation from ETT to WTT.

### What about the rest?

The remaining files are focused on a final translation from the WTT used above
to a simpler version where syntactic sugar is removed.
This part is still work in progress.
