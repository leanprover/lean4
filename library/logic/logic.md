logic
=====

Logical constructions and theorems, beyond what has already been
declared in init.datatypes and init.logic.

The command `import logic` does not import any axioms by default.

* [connectives](connectives.lean) : the propositional connectives
* [eq](eq.lean) : additional theorems for equality and disequality
* [cast](cast.lean) : casts and heterogeneous equality
* [quantifiers](quantifiers.lean) : existential and universal quantifiers
* [identities](identities.lean) : some useful identities
* [instances](instances.lean) : class instances for eq and iff
* [subsingleton](subsingleton.lean)
* [default](default.lean)

The file `choice.lean` declares a choice axiom, and uses it to
prove the excluded middle, propositional completeness, axiom of
choice, and prove that the decidable class is trivial when the
choice axiom is assumed.

* [choice](choice.lean)

Subfolders:

* [examples](examples/examples.md)