# Bundled iterators tailored for verification

## Goals

* Reduce the number of type dependencies and the complexity of instance parameters
* Reduce the complexity of termination
* Provide better equality

## Design Questions

* Include plausibility predicates?
  * Pro: helps reasoning about termination *after* normalizing to bundled iterators
  * Con: so much more complexity
* Use `grind norm` for normalization or some `enter_proof` tactic?

## Wild Ideas

* Change how `outParams` in classes work?
  * Implemented as instance fields, but can be used with the `with` syntax in instance parameters -> unification
