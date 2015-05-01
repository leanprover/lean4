The Lean Homotopy Type Theory Library
=====================================

The Lean homotopy type theory library is contained in the following
modules and directories:

* [init](init/init.md) : constants and theorems needed for low-level system operations
* [types](types/types.md) : concrete datatypes and type constructors
* [hit](hit/hit.md): higher inductive types
* [algebra](algebra/algebra.md) : algebraic structures
* [cubical](cubical/cubical.md) : implementation of ideas from cubical type theory
* [arity](arity.hlean) : a file containing theorems about functions with arity 2 or higher

Lean's homotopy type theory kernel is a version of Martin-Löf Type Theory with:

* universe polymorphism
* a non-cumulative hierarchy of universes, `Type 0`, `Type 1`, ...
* inductively defined types

Note that there is no proof-irrelevant or impredicative universe.

By default, the univalence axiom is declared on initialization.

See also the [standard library](../library/library.md).
