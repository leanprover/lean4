The Lean Library
================

The Lean library is contained in the following modules and directories:

* [init](init/init.md) : constants and theorems needed for low-level system operations
* [logic](logic/logic.md) : logical constructs and axioms
* [data](data/data.md) : concrete datatypes and type constructors
* [algebra](algebra/algebra.md) : algebraic structures
* [tools](tools/tools.md) : additional tools

Modules can be loaded individually, but they are also be loaded by importing the
following packages:

* [standard](standard.lean) : constructive logic and datatypes
* [classical](classical.lean) : classical mathematics

Lean's default logical framework is a version of the Calculus of Constructions with:

* an impredicative, proof-irrelevant type `Prop` of propositions
* universe polymorphism
* a non-cumulative hierarchy of universes, `Type 1`, `Type 2`, ... above `Prop`
* inductively defined types

The `standard` library does not rely on any axioms beyond this framework, and is
hence constructive. It includes theories of the natural numbers, integers,
lists, and so on.

The `classical` library imports the law of the excluded middle, choice functions,
and propositional extensionality. See `logic/axioms` for details.

See also the `hott` library, a library for homotopy type theory based on a predicative 
foundation.
