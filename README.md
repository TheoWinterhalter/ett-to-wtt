# Translation from ETT to ITT

Formalisation (in Coq) of a translation from extensional type theory
to intensional type theory.

## Requirements

This project can be compiled with Coq 8.8 and requires
[Equations](http://mattam82.github.io/Coq-Equations/) 
and [TemplateCoq](https://github.com/Template-Coq/template-coq/tree/coq-8.8)
to compile (probably best to `make && make install` before they release).

If you want to compile the examples, you also need
[TypingFlags](https://github.com/SimonBoulier/TypingFlags).

## Building

Once you have the dependencies (at least Equations), simply run
```bash
make
```
to build the project (it takes quite some time unfortunately, so you
can use options like `-j4` to speed up a little bit).


### Structure of the project

All of the formalisation can be found in the `theories` directory.

*The file [util.v](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/util.v)
provides useful lemmata that aren't specific to the formalisation.*

#### Syntax

First, [Sorts](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Sorts.v) introduces a
notion of sort (as a type-class) stating the basic properties required, and provides different instances
like the natural number hierarchy, type-in-type, or even HTS/2-level TT.
In [SAst](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/SAst.v)
we define the common syntax to both ETT (Extensional type theory) and ITT (our own version of Itensional
type theory with some sugar) in the form of a simple inductive type `sterm`.
Since terms (`sterm`) are annotated with names—for printing—which are
irrelevant for computation and typing, we define an erasure map `nl : sterm -> nlterm`
in [Equality](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Equality.v)
from which we derive a decidable equality on `sterm`.
We then define lifting operations, substitution and closedness in
[SLiftSubst](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/SLiftSubst.v).

#### Typing

First, in [SCommon](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/SCommon.v)
we define common utility to both ETT and ITT, namely with the definition of contexts (`scontext`) and global
contexts (`sglobal_context`), the latter containing the declarations of constants.
[Conversion](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Conversion.v)
is about the untyped conversion used in ITT (conversion `Σ |-i t = u` is derived from one-step reduction
`Σ |-i t ▷ u`) and contains the **only axiom** of the whole formalisation.
[XTyping](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/XTyping.v)
contains the definition of typing rules of ETT (`Σ ;;; Γ |-x t : A`), mutually defined with a typed
conversion (`Σ ;;; Γ |-x t = u : A`) and the well-formedness of contexts (`wf Σ Γ`).
[ITyping](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ITyping.v)
is the same for ITT with the difference that the conversion isn't mutually defined but instead the
one defined in [Conversion](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Conversion.v))
and that it also defines a notion of well-formedness of global declarations (`type_glob Σ`).

#### Lemmata regarding ITT

In [ITypingInversions](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ITypingInversions.v)
one can find an inversion lemma for each constructor of the syntax, together with the tactic `ttinv`
to apply the right one.
In [ITypingLemmata](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ITypingLemmata.v)
are proven a list of different lemmata regarding ITT, including the fact that whenever we have
`Σ ;;; Γ |-i t : A` then `A` is well sorted and that lifting and substitution preserve typing.
Context conversion and the associated typing preservation lemma are found in
[ContextConversion](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ContextConversion.v).
A uniqueness of typing lemma (if `Σ ;;; Γ |-i t :A` and `Σ ;;; Γ |-i t :B` then `Σ |-i A = B`) is proven in
[Uniqueness](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Uniqueness.v).
Subject reduction and the corollary that we call subject conversion (whenever two terms are convertible
and well-typed, their types are also convertible) are proven in
[SubjectReduction](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/SubjectReduction.v).
[ITypingAdmissible](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ITypingAdmissible.v)
states admissible rules in ITT.

#### Translation

[PackLifts](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/PackLifts.v)
defines the lifting operations related to packing. Packing consists in taking two types `A1` and `A2`
and yielding the following record type (where `x ≅ y` stands for heterogenous equality between `x` and `y`).
```coq
Record Pack A1 A2 := pack {
  ProjT1 : A1 ;
  ProjT2 : A2 ;
  ProjTe : ProjT1 ≅ ProjT2
}.
```
In order to produce terms as small / efficient as possible, we provide
*optimised* versions of some constructors, for instance, transport
between two syntactically equal terms is remapped to
identity. Thanks to this, terms that live in ITT should be
translated to themselves syntactically (and not just up to transport).
This is done in
[Optim](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Optim.v).
[FundamentalLemma](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/FundamentalLemma.v)
contains the proof of the fundamental lemma, crucial step for our translation.
[Translation](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Translation.v)
contains the translation from ETT to ITT.

#### Meta Theory of ETT

In order to write ETT derivations more effectively, we develop some of the meta-theory of ETT.
[XInversions](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/XInversions.v) provides
inversion lemmata for ETT while
[XTypingLemmata](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/XTypingLemmata.v) provides
lift and substitution lemmata, along with the proof that the type in a judgement is well sorted.

#### Checking

For type checking, we write one tactic for ITT and one for ETT.
Their respective definitions can be found in
[IChecking](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/IChecking.v) and
[XChecking](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/XChecking.v).

#### Interaction with (Template)Coq

To realise the sugar of ITT, we define some constants in
[Quotes](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Quotes.v)
and then quote them to TemplateCoq's inner representation of terms.
The translation from ITT to TemplateCoq is done in
[FinalTranslation](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/FinalTranslation.v).
[FullQuote](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/FullQuoten.v)
is for the opposite: generating an ITT term from a TemplateCoq (and
thus Coq) term, it is useful to generate examples.
[ExampleQuotes](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ExampleQuotes.v)
is about defining terms that will be useful for examples but need quoting.
The module [ExamplesUtil](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/ExamplesUtil.v)
provides useful lemmata and the proof of well-formedness of a global
context with `nat` and `vec` as axiomatised constants.
Finally, some examples can be found in
[Example](https://github.com/TheoWinterhalter/ett-to-itt/blob/master/theories/Example.v).
