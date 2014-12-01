logic
=====

Additional constructions and axioms. By default, `import logic` does not
import any axioms.

Logical operations and connectives.

* [eq](eq.lean) : additional theorems for equality and disequality
* [cast](cast.lean) : casts and heterogeneous equality
* [quantifiers](quantifiers.lean) : existential and universal quantifiers
* [identities](identities.lean) : some useful identities

Constructively, inhabited types have a witness, while nonempty types
are "proof irrelevant". Classically (assuming the axioms in
logic.axioms.hilbert) the two are equivalent. Type class inferences
are set up to use "inhabited" however, so users should use that to
declare that types have an element. Use "nonempty" in the hypothesis
of a theorem when the theorem does not depend on the witness chosen.

* [axioms](axioms/axioms.md) : additional axioms
* [examples](examples/examples.md)