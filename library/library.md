The Lean Standard Library
=========================

The Lean standard library is contained in the following files and directories:

* [init](init/init.md) : constants and theorems needed for low-level system operations
* [logic](logic/logic.md) : logical constructs and axioms
* [data](data/data.md) : concrete datatypes and type constructors
* [algebra](algebra/algebra.md) : algebraic structures
* [theories](theories/theories.md) : more domain-specific theories
* [tools](tools/tools.md) : additional tools

The files in `init` are loaded by default, and hence do not need to be
imported manually.  Other files can be imported individually, but the
following is designed to load most of the standard library:

* [standard](standard.lean) : constructive logic and datatypes

Lean's default logical framework is a version of the Calculus of
Constructions with:

* an impredicative, proof-irrelevant type `Prop` of propositions
* universe polymorphism
* a non-cumulative hierarchy of universes, `Type 1`, `Type 2`, ... above `Prop`
* inductively defined types
* quotient types

Most of the `standard` library does not rely on any axioms beyond this
framework, and is hence fully constructive.

The following additional axioms are defined in `init`:

* quotients and propositional extensionality (in `quot`)
* Hilbert choice (in `classical`)

Function extensionality is derived from the quotient construction, and
excluded middle is derived from Hilbert choice. For Hilbert choice and
excluded middle, use `open classical`. The additional axioms are used
sparingly. For example:

* The constructions of finite sets and the rationals use quotients.
* The set library uses propext and funext, as well as excluded middle to prove 
  some classical identities.
* Hilbert choice is used to define the multiplicative inverse on the reals, and 
  also to define function inverses classically.

You can use `print axioms foo` to see which axioms `foo` depends
on. Many of the theories in the `theories` folder are unreservedly
classical.

See also the [hott library](../hott/hott.md), a library for homotopy
type theory based on a predicative foundation.
