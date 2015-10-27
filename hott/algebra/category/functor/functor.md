algebra.category.functor
========================

Functors, functor attributes, equivalences, isomorphism, adjointness.

* [basic](basic.hlean) : Definition and basic properties of functors
* [examples](examples.hlean) : Constructions of functors between categories, involving more than one category in the [constructions](../constructions/constructions.md) folder (functors which only depend on one constructions are in the corresponding file). This includes the currying and uncurrying of functors
* [attributes](attributes.hlean): Attributes of functors (full, faithful, split essentially surjective, ...)
* [adjoint](adjoint.hlean) : Adjoint functors and equivalences
* [equivalence](equivalence.hlean) : Equivalences and Isomorphisms
* [exponential_laws](exponential_laws.hlean)
* [yoneda](yoneda.hlean) : the Yoneda Embedding

Note: the functor category is defined in [constructions.functor](../constructions/functor.hlean). Functors preserving limits is in [limits.functor_preserve](../limits/functor_preserve.hlean).