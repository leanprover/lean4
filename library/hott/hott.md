standard.hott
=============

A library for Homotopy Type Theory, which avoid the use of prop. Many
standard types are imported from `standard.data`, but then theorems
are proved about them using predicate versions of the logical
operations. For example, we use the path type, products, sums, sigmas,
and the empty type, rather than equality, and, or, exists, and
false. These operations take values in Type rather than Prop.

We view Homotopy Theory Theory as compatible with the axiomatic
framework of Lean, simply ignoring the impredicative, proof irrelevant
Prop. This is o.k. as long as we do not import additional axioms like
propositional extensionality or Hilbert choice, which are incompatible
with HoTT.

* [path](path.lean) : the path type and operations on paths
* [equiv](equiv.lean) : equivalence of types
* [trunc](trunc.lean) : truncatedness of types
* [funext](funext.lean) : the functional extensionality axiom
* [inhabited](inhabited.lean) : a predicative version of the inhabited class
