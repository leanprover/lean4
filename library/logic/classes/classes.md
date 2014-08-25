logic.classes
=============

Useful classes for general logical manipulations.

* [inhabited](inhabited.lean) : inhabited types
* [nonempty](nonempty.lean) : nonempty type
* [decidable](decidable.lean) : decidable types

Constructively, inhabited types have a witness, while nonempty types
are "proof irrelevant". Classically (assuming the axioms in
`logic.axioms.hilbert`) the two are equivalent. Type class inferences
are set up to use "inhabited" however, so users should use that to
declare that types have an element. Use "nonempty" in the hypothesis
of a theorem when the theorem does not depend on the witness chosen.