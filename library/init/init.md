init
====

The files in this folder are required by low-level operations, and
are always imported by default. You can suppress this behavior by
beginning a file with the keyword "prelude".

Syntax declarations:

* [reserved_notation](reserved_notation.lean)
* [tactic](tactic.lean)

Datatypes and logic:

* [datatypes](datatypes.lean)
* [logic](logic.lean)
* [classical](classical.lean)
* [bool](bool.lean)
* [num](num.lean)
* [nat](nat.lean)

Support for well-founded recursion:

* [relation](relation.lean)
* [wf](wf.lean)
* [wf_k](wf_k.lean)
* [measurable](measurable.lean)

Additional datatypes:

* [prod](prod.lean)
* [sigma](sigma.lean)

The default import:

* [default](default.lean)

Module init.logic defines "inhabited" and "nonempty"
types. Constructively, inhabited types have a witness, while nonempty
types are proof irrelevant. Classically (assuming the axioms in
logic.axioms.hilbert) the two are equivalent. Type class inferences
are set up to use "inhabited" however, so users should use that to
declare that types have an element. Use "nonempty" in the hypothesis
of a theorem when the theorem does not depend on the witness chosen.

Module init.classical declares a choice axiom, and uses it to
prove the excluded middle, propositional completeness, axiom of
choice, and prove that the decidable class is trivial when the
choice axiom is assumed.
