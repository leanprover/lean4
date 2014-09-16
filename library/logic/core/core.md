logic.core
==========

Logical operations and connectives.

* [prop](prop.lean) : the type Prop
* [eq](eq.lean) : equality and disequality
* [connectives](connectives.lean) : propositional connectives
* [cast](cast.lean) : casts and heterogeneous equality
* [quantifiers](quantifiers.lean) : existential and universal quantifiers
* [if](if.lean) : if-then-else
* [identities](identities.lean) : some useful identities
* [examples](examples/examples.md)

Type classes for general logical manipulations:

* [inhabited](inhabited.lean) : inhabited types
* [nonempty](nonempty.lean) : nonempty type
* [decidable](decidable.lean) : decidable types
* [instances](instances.lean) : type class instances

Constructively, inhabited types have a witness, while nonempty types
are "proof irrelevant". Classically (assuming the axioms in
logic.axioms.hilbert) the two are equivalent. Type class inferences
are set up to use "inhabited" however, so users should use that to
declare that types have an element. Use "nonempty" in the hypothesis
of a theorem when the theorem does not depend on the witness chosen.


