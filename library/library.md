The Lean Library
================

The Lean library is contained in the following modules and directories:

* [general_notation](general_notation.lean) : commonly shared notation
* [logic](logic/logic.md) : logical constructs and axioms
* [data](data/data.md) : concrete datatypes and type constructors
* [struc](struc/struc.md) : axiomatic structures
* [hott](hott/hott.md) : homotopy type theory
* [tools](tools/tools.md) : additional tools

Modules can be loaded individually, but they are also be loaded by importing the
following packages:

* [standard](standard.lean) : constructive logic and datatypes
* [classical](classical.lean) : classical mathematics
* [hott](hott/default.lean) : homotopy type theory

Lean's default logical framework is a version of the Calculus of Constructions with:

* an impredicative, proof-irrelevant type `Prop` of propositions
* a non-cumulative hierarchy of universes, `Type 1`, `Type 2`, ... above `Prop`
* inductively defined types

The `standard` library does not rely on any axioms beyond this framework, and is
hence constructive. It includes theories of the natural numbers, integers,
lists, and so on.

The `classical` library imports the law of the excluded middle, choice functions,
and propositional extensionality. See `logic/axioms` for details.

The `hott` library is compatible with the standard library, but favors "proof
relevant" versions of the logical connectives, based on `Type` rather than
`Prop`. See `hott` for details.