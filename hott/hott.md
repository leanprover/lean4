The Lean Homotopy Type Theory Library
=====================================

The Lean homotopy type theory library is contained in the following
files and directories:

* [init](init/init.md) : constants and theorems needed for low-level system operations
* [types](types/types.md) : concrete datatypes and type constructors
* [hit](hit/hit.md): higher inductive types
* [algebra](algebra/algebra.md) : algebraic structures
* [arity](arity.hlean) : a file containing theorems about functions with arity 2 or higher

See [book.md](book.md) for an overview of the sections of the [HoTT book](http://homotopytypetheory.org/book/) which have been covered.

Lean's homotopy type theory kernel is a version of Martin-Löf Type Theory with:

* universe polymorphism
* a non-cumulative hierarchy of universes, `Type 0`, `Type 1`, ...
* inductively defined types
* [Two HITs](init/hit.hlean): `n`-truncation and quotients.

Note that there is no proof-irrelevant or impredicative universe.

By default, the univalence axiom is declared on initialization.

See also the [standard library](../library/library.md).
