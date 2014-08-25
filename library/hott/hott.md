standard.hott
=============

A library for homotopy type theory. HoTT is consistent with the
existence of an imprediative, proof irrelevant `Prop`, but favors
"proof relevant," predicative versions of the usual logical
constructions. For example, we use the path type, products, sums,
sigmas, and the empty type, rather than equality, and, or, exists, and
false. These operations take values in `Type` rather than `Prop`.

Note that the univalence axiom is inconsistent with classical axioms
such as propositional extensionality or Hilbert choice, and we have to
ensure that the library does not import these.

The modules imported by the command `import hott` are found in the
file [default](default.lean).

* [path](path.lean) : the path type and operations on paths
* [equiv](equiv.lean) : equivalence of types
* [trunc](trunc.lean) : truncatedness of types
* [funext](funext.lean) : the functional extensionality axiom
* [fibrant](fibrant.lean) : a class for fibrant types
