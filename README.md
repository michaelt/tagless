# Typed tagless-final interpretations: Lecture notes

 

The course on typed tagless-final embeddings of
domain-specific languages has been presented at
the Spring School on Generic and Indexed
Programming (SSGIP) [http://www.comlab.ox.ac.uk/projects/gip/school.html](http://www.comlab.ox.ac.uk/projects/gip/school.html)
at Wadham College, Oxford, UK on 22nd to 26th
March 2010. This page collects the notes for the
course in the form of the extensively commented
Haskell and OCaml code.

--------------------------

## Introduction

The topic of the course is the embedding of
domain-specific languages (DSL) in a host language
such as Haskell or OCaml. We will often call the
language to embed 'the object language' and the
host language 'the metalanguage'. All throughout
the course we will repeatedly encounter the
following points:

-   Multiple interpretations:
    -   writing a DSL program once, and interpret
        it many times, in standard and
        non-standard ways;

-   Extensibility:
    -   enriching the syntax of the object
        language, re-using but not breaking the
        existing interpreters;

-   *Types*

-   Typed implementation language
    -   getting the typechecker to verify
        properties of interpreters, such as not
        getting stuck;

-   Typed object language
    -   getting the metalanguage typechecker to
        enforce properties of DSL programs, such
        as being well-typed;

-   Connections with logic

-   Final
    -   preferring lower-case
    -   preferring elimination over introduction
    -   connecting to denotational semantics

# First-order languages (generic programming)

We will be talking about ordinary data types and
(generic) operations on them. The expression
problem will make its appearance. The first-order
case makes it easier to introduce de-serialization
and seemingly non-compositional operations.

 

## Initial and final, deep and shallow: the first-order case

[Intro1.hs](Intro1.hs) [2K]  Algebraic data type/initial representation of expressions;  Constructor functions: the intimation of the final representation (or, shallow embedding)

[Intro2.hs](Intro2.hs) [3K] Symantics: parameterization of terms by interpreters

[Intro3.hs](Intro3.hs) [2K] Initial and Final, Deep and Shallow, First-class

[ExtI.hs](ExtI.hs) [<1K] Algebraic data types are indeed not extensible

[ExtF.hs](ExtF.hs) [2K] Adding a new expression form to the final view: solving the expression problem

[Serialize.hs](Serialize.hs) [4K] Serialization and de-serialization

[SerializeExt.hs](SerializeExt.hs) [4K] De-serializing the extended language

 

## Final embeddings in OCaml

We demonstrate several encodings of extensible
first-order languages in OCaml. Objects turn out
handy in emulating the composition of type class
dictionaries. 

[final_obj.ml](final_obj.ml) [2K] The traditional application of objects to represent extensible data types. Alas, the set of operations on these data types is not extensible.

[final_mod.ml](final_mod.ml) [3K] Tagless-final embedding using modules

[final_dic.ml](final_dic.ml) [3K] Tagless-final embedding with objects emulating type-class dictionaries. Both the language and the set of its interpretations are extensible.

 

## Non-compositionality: Fold-*unlike* processing

Interpreters are well suited for compositional,
fold-like operations on terms. The tagless-final
representation of terms makes writing interpreters
quite convenient. One may wonder about operations
on terms that do not look like fold. Can we even
pattern-match on terms represented in the
tagless-final style? Can we compare such terms for
equality? We answer the first question here,
deferring the equality test till the part on
implementing a type checker for a higher-order
language. Our running examples are term
transformations, converting an expression into a
simpler, more optimal, or canonical form. The
result is an uncrippled expression, which we can
feed into any of the existing or future
interpreters. Our sample term transformations look
like simplified versions of the conversion of a
boolean formula into a conjunctive normal form.

[PushNegI.hs](PushNegI.hs) [3K] Pushing the negation down: the initial implementation

[PushNegF.hs](PushNegF.hs) [3K] Pushing the negation down: the final implementation

[PushNegFExt.hs](PushNegFExt.hs) [4K] Pushing the negation down for extended tagless-final terms

[FlatI.hs](FlatI.hs) [2K]

[FlatF.hs](FlatF.hs) [3K] Flattening of additions, the initial and the final implementations

[PushNegFI.hs](PushNegFI.hs) [3K] The final-initial isomorphism, and its use for
implementing arbitrary pattern-matching operations on tagless-final terms.

[http://www.comlab.ox.ac.uk/ralf.hinze/SSGIP10/Slides.pdf](http://www.comlab.ox.ac.uk/ralf.hinze/SSGIP10/Slides.pdf)

Ralf Hinze, in Part 7 of his Spring School course,
has derived this 'initial-final' isomorphism
rigorously, generally and elegantly from the point
of view of Category Theory. In the first-order
case, both 'initial' and 'final' are the left
and the right views to the same Initial Algebra.
The 'final' view is, in the first-order case,
ordinary Church encoding.

# Interpreters for higher-order languages

Higher-order languages are data types with
binding, so to speak. In the first part, only the
interpreters were typed; we could get away with
our object language being unityped. Now, the
object language itself becomes typed, bringing the
interesting issues of interpreting a typed
language in a type language ensuring type
preservation. It is this part that explains the
attributes 'typed' and 'tagless' in the title of
the course.

 

## Type-preserving embedding of higher-order, typed DSLs

Using simply-typed lambda-calculus with constants
as a sample DSL, we demonstrate its various
embeddings into Haskell. We aim at a
type-preserving embedding and efficient and
type-preserving evaluations. The tagless-final
embedding not only achieves this goal, it also
makes the type-preservation patently clear.
Tagless-final evaluators are well-typed Haskell
programs with no pattern-matching on variant
types. It becomes impossible for the evaluators to
get stuck. Since the type preservation of the
evaluators is apparent not only to us but also to
a Haskell compiler, the evaluators can be
efficiently compiled. Tagless-final embeddings are
also extensible, letting us add to the syntax of
the DSL, preserving and reusing old interpreters.

[IntroHOT.hs](IntroHOT.hs) [3K] The illustration of problems of embedding a typedDSL into a typed metalanguage

Either the Universal type (and hence spurious
partiality, type tags and inefficiency), or fancy
type systems seem inevitable. The problem stems
from algebraic data types' being too broad: they
express not only well-typed DSL terms but also
ill-typed ones.

[Term.agda](Term.agda) [2K]
[http://www.iis.sinica.edu.tw/\~scm/2008/typed-lambda-calculus-interprete/](http://www.iis.sinica.edu.tw/~scm/2008/typed-lambda-calculus-interprete/)

Shin-Cheng Mu: Typed Lambda-Calculus Interpreter in Agda. September 24, 2008

Shin-Cheng Mu solves the problem of the
type-preserving tagless interpretation of
simply-typed lambda-calculus, relying on dependent
types and type functions in full glory.

[IntroHOIF.hs](IntroHOIF.hs) [6K] Tagless-initial and Tagless-final evaluators

[TTFdB.hs](TTFdB.hs) [7K] Typed, tagless, final, with de Bruijn indices:
Expressing the type system of simply-typed
lambda-calculus in Haskell98. No dependent types
are necessary after all. The types of methods in
the Symantics type class read like the axioms and
inference rules of the implication fragment of
minimal logic.

[TTF.hs](TTF.hs) [7K] Typed, tagless, final, in the higher order
abstract syntax (HOAS). We illustrate extending
the DSL with more constants, types, and expression
forms.

[TTIF.hs](TTIF.hs) [8K] Initial-final isomorphism, in the higher-order case

 

## De-serialization and type-checking

Since we represent DSL expressions as well-typed
Haskell terms, we can place DSL terms in Haskell
code or enter at the GHCi prompt. However, we also
want to interpret DSL expressions that are read
from files or received from communication pipes.
We no longer can then rely on GHC to convert DSL
expressions from a text format into the typed
embedding. We have to do the type-checking of DSL
expressions ourselves. Our goal is to type-check
an expression once, during de-serialization, and
evaluate the result many times. Since a type
checker needs to represent types and reason about
type equality, we develop type representations and
type safe cast. We regard the language of types,
too, as a typed DSL, which we embed in Haskell in
the tagless-final style.

[TypeCheck.hs](TypeCheck.hs) [12K]\ De-serialization: (Dynamic) Type Checking\
In contrast to an earlier version of the type
checker, we use de Bruijn indices and obtain a
much clearer code. The code is quite similar to
Baars and Swierstra's ''Typing Dynamic Typing''
(ICFP02). However, the result of our type-checking
is an embedded DSL expression that can be
interpreted many times and in many ways, rather
than being merely evaluated. The set of possible
interpretations is open. Also, our code is written
to expose more properties of the type-checker for
verification by the Haskell type-checker; for
example, that closed source terms are
de-serialized into closed target terms.

[Typ.hs](Typ.hs) [8K] Type representation, equality and the type-safe generalized cast

We present an above-the-board version of
`Data.Typeable`, in the tagless-final style. Our
implementation uses no GHC internal operations, no
questionable extensions, or even a hint of unsafe
operations.

[http://www.comlab.ox.ac.uk/projects/gip/school/tc.hs](http://www.comlab.ox.ac.uk/projects/gip/school/tc.hs)

Stephanie Weirich some time ago wrote a very
similar type-checker, but in the initial style,
using GADTs. The comparison with the tagless-final
style here is illuminating.

# Applications and Extensions

 

## Ordinary and one-pass CPS transformation

We demonstrate ordinary and
administrative-redex--less call-by-value
Continuation Passing Style (CPS) transformation
that assuredly produces well-typed terms and is
*patently* total. Our goal here is not to
evaluate, view or serialize a tagless-final term,
but to transform it to another one. The result is
a tagless-final term, which we can interpret in
multiple ways: evaluate, view, or transform again.
We first came across transformations of
tagless-final terms when we discussed pushing the
negation down in the simple, unityped language of
addition and negation. The general case is more
complex. It is natural to require the result of
transforming a well-typed term be well-typed. In
the tagless-final approach that requirement is
satisfied automatically: after all, only
well-typed terms are expressible. We require
instead that a tagless-final transformation be
total. In particular, the fact that the
transformation handles all possible cases of the
source terms must be patently, syntactically
clear. The complete coverage must be so clear that
the metalanguage compiler should be able to see
that, without the aid of extra tools.

Since the only thing we can do with tagless-final
terms is to interpret them, the CPS transformer is
written in the form of an interpreter. It
interprets source terms yielding transformed
terms, which can be interpreted in many ways. In
particular, the terms can be interpreted by the
CPS transformer again, yielding 2-CPS terms. CPS
transformers are composable, as expected.

A particular complication of the CPS transform is
that the type of the result is different from the
type of the source term: the CPS transform
translates not only terms but also types.
Moreover, the CPS type transform and the arrow
type constructor do not commute. For that reason,
we have to introduce an extended Symantics class,
ESymantics, which makes the meaning of function
types dependent on a particular interpreter. As it
turns out, we do not have to re-write the existing
Symantics terms: we can re-interpret any old terms
in the extended Symantics. Conversely, any
extended Symantics term can be interpreted using
any old, legacy, Symantics interpreter. The CPS
transform is an extended Symantics interpreter
proper.

The ordinary (Fischer or Plotkin) CPS transform
introduces many administrative redices, which make
the result too hard to read. Danvy and Filinski
proposed a one-pass CPS transform, which relies on
the metalanguage to get rid of the administrative
redices. The one-pass CPS transform can be
regarded as an example of the
normalization-by-evaluation.

[CPS.hs](CPS.hs) [12K] Ordinary and one-pass CPS transforms and their
compositions

Olivier Danvy and Andrzej Filinski. Representing
Control: A Study of the CPS Transformation.\
Mathematical Structures in Computer Science, 1992.

 

## Type-directed partial evaluation

Olivier Danvy's original POPL96 paper on
type-directed partial evaluation used an untyped
target language, represented as an algebraic data
type. Type preservation was not apparent and had
to be proved. In our presentation, the result of
reification is a *typed* expression, in the
tagless-final form. Type preservation of
reification is now syntactically apparent and is
verified by the Haskell type-checker. In the
tagless-final presentation, reification and
reflection seem particularly symmetric, elegant
and insightful. 

[TDPE.hs](TDPE.hs) [6K] Tagless-final presentation of type-directed
partial evaluation

[ToTDPE.hs](ToTDPE.hs) [<1K] The imported module with sample functions to
reify. Compiling this module makes for a nicer
example.

[http://www.brics.dk/\~danvy/tdpe-ln.pdf](http://www.brics.dk/~danvy/tdpe-ln.pdf)

Olivier Danvy: Lecture notes on type-directed
partial evaluation. The lecture notes are based on
his POPL96 paper.

 

## Linear and affine lambda-calculi

One may think that we can embed in Haskell only
those DSL whose type system is a subset of that of
Haskell. We will now attempt to break that
impression by showing how to embed typed *linear*
lambda calculus. Any bound variable must be
referenced exactly once in abstraction's body. As
before, our embedding makes sure that only
well-typed and well-formed terms are
representable. In other words, Haskell as the
metalanguage will statically reject as ill-typed
representations of lambda-terms in which the bound
variable appears several times -- or, as in the K
combinator, never. Our approach relies on de
Bruijn representation for variables. We have
already discussed the tagless-final encoding for
the ordinary simply-typed lambda calculus with de
Bruijn indices. An object term of the type `a` was
represented as a value of the type `repr h a`
where the binary type constructor `repr` is a
member of the class `Symantics`. The type variable
`h` represents the variable (or, hypothetical)
environment, describing the types of term's free
variables. In linear lambda calculus, terms
associated with bound variables are regarded as
resources; referencing a variable consumes the
resource. We use the variable environment for
tracking the state of resources: available, or
consumed. Since evaluating an expression may
'consume' a resource associated with one of
expression's variables, the variable environment
becomes the variable *state*. We can then follow
the approach described in [Variable (type)state'monad'](../../Computation/monads.html#param-monad).

We represent linear lambda terms by Haskell values
of the type `repr hi ho a`, where `hi` stands for
the variable state before evaluating the term and
`ho` stands for the state after evaluating the
term. To be more precise, `hi` and `ho` are the
types of the variable states. We can determine the
types and hence the state of the variables
statically: As usual, the type checker does
abstract interpretation. In our tagless-final
encoding, `lam` has the following type

    lam :: repr (F a,hi) (U,ho) b  -> repr hi ho (a->b)

The expression `(lam e)` has the type
`repr hi ho (a->b)` provided the body of
abstraction, `e`, has the type
`repr (F a,hi) (U,ho) b`. That is, in the
environment extended with a term of the type `a`,
the body must produce the value of type `b`. The
body must consume the term at the top of the
environment, changing the type of the first
environment cell from `F a` to `U` (the type of
the used variable). A trivial modification turns
the embedding of the linear lambda-calculus into
the embedding of the affine lambda-calculus,
permitting no references to the bound variable
within the abstraction body. K combinator becomes
expressible.

[LinearLC.hs](LinearLC.hs) [11K]\
Commented code defining the typed linear lambda
calculus and its two interpreters, to evaluate and
to show linear lambda terms. The code demonstrates
extending the linear calculus by adding general
abstractions imposing no constraints on the use of
bound variables.

 

## Further applications

-   [CBAny.hs](CBAny.hs) [7K]\
     Parameterizing evaluators by the evaluation
    order: call-by-name, call-by-value,
    call-by-need\
     [CB98.hs](../CB98.hs) [7K]\
     The same, but in pure Haskell 98
-   [PrintScanF.hs](PrintScanF.hs) [8K]\
     Typed formatting: printf and scanf. The code
    is one of the implementations of [Type-safe
    Formatted IO](../../typed-formatting/).
-   Sandro Magi: Mobile Code in C\# via Finally
    Tagless Interpreters. June 23, 2009.\
     [http://higherlogics.blogspot.com/2009/06/mobile-code-in-c-via-finally-tagless.html](http://higherlogics.blogspot.com/2009/06/mobile-code-in-c-via-finally-tagless.html)

    Sandro Magi shows that different
    interpretations of the same DSL term may not
    only involve different run-time systems but
    also occur on different hosts.
-   Expressing sharing
-   Non-standard and abstract interpretations
-   Unusual calculi: shift/reset with effect
    typing; lambda-mu-mubar
-   Abstract Categorial Grammars  [http://www.loria.fr/equipes/calligramme/acg](http://www.loria.fr/equipes/calligramme/acg)

* * * * *

### Last updated June 7, 2010

This site's top page is
[**http://okmij.org/ftp/**](http://okmij.org/ftp/)
oleg-at-pobox.com or oleg-at-okmij.org\
Your comments, problem reports, questions are very
welcome!

Converted from HSXML by HSXML->HTML
