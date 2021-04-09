# Eliminating Reflection from Type Theory
**A translation from extensional type theory (ETT) to weak type theory (WTT)**

*Authors:* Théo Winterhalter, Matthieu Sozeau, Nicolas Tabareau and Simon Boulier

**Quick jump**
- [Installing](#installing)
- [Structure](#structure-of-the-project)

## Overview

This work is a Coq formalisation of a translation from ETT to ITT that can
be interfaced with Coq thanks to the TemplateCoq plugin.
Additionally, sorts are handled quite generically (although without
cumulativity) which means in particular that we can have a translation from
Homotopy Type System (HTS) to Two-Level Type Theory (2TT) as a direct
application.

ETT differs from ITT by the addition of the **reflection rule**:
```
Γ ⊢ e : u = v
--------------
  Γ ⊢ u ≡ v
```

WTT is ITT without any notion of computation or conversion.

## Installing

### Requirements

This project can be compiled with Coq 8.11.0 and requires
[Equations](http://mattam82.github.io/Coq-Equations/)
and [MetaCoq](https://github.com/MetaCoq/metacoq).

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
theory) and ITT (our own version of Itensional type theory with some sugar) in
the form of a simple inductive type `sterm`.
Since terms (`sterm`) are annotated with names—for printing—which are
irrelevant for computation and typing, we define an erasure map
`nl : sterm -> nlterm` in [Equality](theories/Equality.v) from which we derive
a decidable equality on `sterm`.
We then define lifting operations, substitution and closedness in
[SLiftSubst](SLiftSubst.v).

### Typing

First, in [SCommon](theories/SCommon.v) we define common utility to both ETT and
ITT, namely with the definition of contexts (`scontext`) and global
contexts (`sglobal_context`), the latter containing the declarations of
constants.
[Conversion](theories/Conversion.v) is about the untyped conversion used in ITT
(conversion `t ≡ u` is derived from one-step reduction `t ▷ u`) and contains
the **only axiom** of the whole formalisation (stating that conversion
is transitive, this would require us to prove confluence of the
rewriting system, which we deem orthogonal to our proof).
[XTyping](theories/XTyping.v) contains the definition of typing rules of ETT
(`Σ ;;; Γ |-x t : A`), mutually defined with a typed conversion
(`Σ ;;; Γ |-x t ≡ u : A`) and the well-formedness of contexts (`wf Σ Γ`).
[ITyping](theories/ITyping.v) is the same for ITT with the difference that the
conversion isn't mutually defined but instead the one defined in
[Conversion](theories/Conversion.v)) and that it also defines a notion of
well-formedness of global declarations (`type_glob Σ`).

### Lemmata regarding ITT

In [ITypingInversions](theories/ITypingInversions.v) one can find an inversion
lemma for each constructor of the syntax, together with the tactic `ttinv` to
apply the right one.
In [ITypingLemmata](theories/ITypingLemmata.v) are proven a list of different
lemmata regarding ITT, including the fact that whenever we have
`Σ ;;; Γ |-i t : A` then `A` is well sorted and that lifting and substitution
preserve typing.
Context conversion and the associated typing preservation lemma are found in
[ContextConversion](theories/ContextConversion.v).
A uniqueness of typing lemma (if `Σ ;;; Γ |-i t :A` and `Σ ;;; Γ |-i t :B` then
`A ≡ B`) is proven in [Uniqueness](theories/Uniqueness.v).
Subject reduction and the corollary that we call subject conversion
(whenever two terms are convertible and well-typed, their types are also
convertible) are proven in [SubjectReduction](theories/SubjectReduction.v).
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
that live in ITT should be translated to themselves syntactically (and not just
up to transport).
This is done in [Optim](theories/Optim.v), relying on a (semi-)decision
procedure for conversion in ITT defined in
[DecideConversion.v](theories/DecideConversion.v).
[FundamentalLemma](theories/FundamentalLemma.v) contains the proof of the
fundamental lemma, crucial step for our translation.
[Translation](theories/Translation.v) contains the translation from ETT to ITT.

### Meta Theory of ETT

In order to write ETT derivations more effectively, we develop some of the
meta-theory of ETT. [XInversions](theories/XInversions.v) provides inversion
lemmata for ETT while [XTypingLemmata](theories/XTypingLemmata.v) provides lift
and substitution lemmata, along with the proof that the type in a judgement is
well sorted.

### Checking

For type checking, we write one tactic for ITT and one for ETT.
Their respective definitions can be found in
[IChecking](theories/IChecking.v) and [XChecking](theories/XChecking.v).

### TemplateCoq and Plugin

To realise the sugar of ITT, we define some constants in
[Quotes](theories/Quotes.v) and then quote them to TemplateCoq's inner
representation of terms.
The translation from ITT to TemplateCoq is done in
[FinalTranslation](theories/FinalTranslation.v).
[FullQuote](theories/FullQuote.v) is for the opposite: generating an ITT term
from a TemplateCoq (and thus Coq) term, it is useful to generate examples.

Finally [plugin](theories/plugin.v) defines a plugin using the TemplateMonad.
It relies on type checkers written in [plugin_checkers](theories/checker.v)
and some extra utility in [plugin_util](theories/util.v).

**To see the plugin in action, just have a look at [plugin_demo](theories/plugin_demo.v)!**
