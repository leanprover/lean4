The Lean Homotopy Type Theory Library
=====================================

The Lean Homotopy Type Theory library consists of the following directories:

* [init](init/init.md) : constants and theorems needed for low-level system operations
* [types](types/types.md) : concrete datatypes and type constructors
* [hit](hit/hit.md): higher inductive types
* [algebra](algebra/algebra.md) : algebraic structures
* [cubical](cubical/cubical.md): cubical types

The following files don't fit in any of the subfolders:
* [prop_trunc](prop_trunc.hlean): in this file we prove that `is_trunc n A` is a mere proposition. We separate this from [types.trunc](types/trunc.hlean) to avoid circularity in imports.
* [eq2](eq2.hlean): coherence rules for the higher dimensional structure of equality
* [function](function.hlean): embeddings, (split) surjections, retractions
* [arity](arity.hlean) : equality theorems about functions with arity 2 or higher
* [choice](choice.hlean) : theorems about the axiom of choice.

See [book.md](book.md) for an overview of the sections of the [HoTT book](http://homotopytypetheory.org/book/) which have been covered.

Lean's homotopy type theory kernel is a version of Martin-Löf Type Theory with:

* universe polymorphism
* a non-cumulative hierarchy of universes, `Type 0`, `Type 1`, ...
* inductively defined types
* [Two HITs](init/hit.hlean): `n`-truncation and quotients.

Note that there is no proof-irrelevant or impredicative universe.

By default, the univalence axiom is declared on initialization.

See also the [standard library](../library/library.md). We [port](port.md) some files from the standard library to the HoTT library.
