The Lean Core Library
=========================

The Lean core library is contained in the following files and directories:

* [init](init/) : constants and theorems needed for low-level system operations
* [init/logic.lean](init/logic.lean) : logical constructs and axioms
* [init/data](init/data/) : concrete datatypes and type constructors
* [init/algebra](init/algebra/) : algebraic structures

Lean's default logical framework is a version of the Calculus of
Constructions with:

* an impredicative, proof-irrelevant type `Prop` of propositions
* universe polymorphism
* a non-cumulative hierarchy of universes, `Type 0`, `Type 1`, ... above `Prop`
* inductively defined types
* quotient types

Most of the `core` library does not rely on any axioms beyond this
framework, and is hence fully constructive.

The following additional axioms are defined in `init`:

* quotients and propositional extensionality (in `quot`)
* Hilbert choice (in `classical`)

Function extensionality is derived from the quotient construction, and
excluded middle is derived from Hilbert choice. For Hilbert choice and
excluded middle, use `open classical`. The additional axioms are used
sparingly. For example:

You can use `#print axioms foo` to see which axioms `foo` depends
on.
