HoTT Book in Lean
=================

This file lists which sections of the [HoTT book](http://homotopytypetheory.org/book/) have been covered in the Lean [HoTT library](hott.md).

Summary
-------

The rows indicate the chapters, the columns the sections.

* `+`: completely formalized
* `¼`, `½` or `¾`: partly formalized
* `-`: not formalized
* `.`: no formalizable content

|       | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|-------|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|
| Ch 1  | . | . | . | . | + | + | + | + | + | .  | +  | +  |    |    |    |
| Ch 2  | + | + | + | + | . | + | + | + | + | +  | +  | +  | +  | +  | +  |
| Ch 3  | + | + | + | + | ½ | + | + | + | + | .  | +  |    |    |    |    |
| Ch 4  | - | + | + | + | . | + | ½ | + | + |    |    |    |    |    |    |
| Ch 5  | - | . | ½ | - | - | . | . | ½ |   |    |    |    |    |    |    |
| Ch 6  | . | + | + | + | + | ½ | ½ | + | ¾ | ¼  | ¾  | +  | .  |    |    |
| Ch 7  | + | + | + | - | ¾ | - | - |   |   |    |    |    |    |    |    |
| Ch 8  | + | + | + | - | ¼ | ¼ | - | - | - | -  |    |    |    |    |    |
| Ch 9  | ¾ | + | + | ½ | ¾ | ½ | - | - | - |    |    |    |    |    |    |
| Ch 10 | - | - | - | - | - |   |   |   |   |    |    |    |    |    |    |
| Ch 11 | - | - | - | - | - | - |   |   |   |    |    |    |    |    |    |

Theorems and definitions in the library which are not in the book:

* A major difference is that in this library we heavily use pathovers [D. Licata, G. Brunerie. A Cubical Approach to Synthetic Homotopy Theory]. This means that we need less theorems about transports, but instead corresponding theorems about pathovers. These are in [init.pathover](init/pathover.hlean). For higher paths there are [squares](cubical/square.hlean), [squareovers](cubical/squareover.hlean), and the rudiments of [cubes](cubical/cube.hlean) and [cubeovers](cubical/cubeover.hlean).

* The category theory library is more extensive than what is presented in the book. For example, we have [limits](algebra/category/limits/limits.md).

Chapter 1: Type theory
---------

- 1.1 (Type theory versus set theory): no formalizable content.
- 1.2 (Function types): no formalizable content. Related: [init.function](init/function.hlean)
- 1.3 (Universes and families): no formalizable content (Lean also has a hierarchy of universes `Type.{i} : Type.{i + 1}`, but they are *not* cumulative).
- 1.4 (Dependent function types (Π-types)): no formalizable content. Related: [init.function](init/function.hlean)
- 1.5 (Product types): declaration in [init.datatypes](init/datatypes.hlean), notation in [init.types](init/types.hlean)
- 1.6 (Dependent pair types (Σ-types)): declaration in [init.datatypes](init/datatypes.hlean), notation in [init.types](init/types.hlean)
- 1.7 (Coproduct types): declaration in [init.datatypes](init/datatypes.hlean), notation in [init.types](init/types.hlean)
- 1.8 (The type of booleans): declaration in [init.datatypes](init/datatypes.hlean), notation in [init.bool](init/bool.hlean)
- 1.9 (The natural numbers): [init.nat](init/nat.hlean) (declaration in [init.datatypes](init/datatypes.hlean))
- 1.10 (Pattern matching and recursion): no formalizable content (we can use the "pattern matching" notation using the function definition package, which are reduced to applying recursors).
- 1.11 (Propositions as types): some logic is in [init.logic](init/logic.hlean) and [init.types](init/types.hlean).
- 1.12 (Identity types): declaration in [init.datatypes](init/datatypes.hlean), more in [init.logic](init/logic.hlean)

Chapter 2: Homotopy type theory
---------

- 2.1 (Types are higher groupoids): [init.path](init/path.hlean) (pointed types and loop spaces in [types.pointed](types/pointed.hlean))
- 2.2 (Functions are functors): [init.path](init/path.hlean)
- 2.3 (Type families are fibrations): [init.path](init/path.hlean)
- 2.4 (Homotopies and equivalences): homotopies in [init.path](init/path.hlean) and equivalences in [init.equiv](init/equiv.hlean)
- 2.5 (The higher groupoid structure of type formers): no formalizable content
- 2.6 (Cartesian product types): [types.prod](types/prod.hlean)
- 2.7 (Σ-types): [types.sigma](types/sigma.hlean)
- 2.8 (The unit type): special case of [init.trunc](init/trunc.hlean)
- 2.9 (Π-types and the function extensionality axiom): [init.funext](init/funext.hlean), [types.pi](types/pi.hlean) and [types.arrow](types/arrow.hlean)
- 2.10 (Universes and the univalence axiom): [init.ua](init/ua.hlean)
- 2.11 (Identity type): [init.equiv](init/equiv.hlean) (ap is an equivalence), [types.eq](types/eq.hlean) and [cubical.square](cubical/square.hlean) (characterization of pathovers in equality types)
- 2.12 (Coproducts): [types.sum](types/sum.hlean)
- 2.13 (Natural numbers): [types.nat.hott](types/nat/hott.hlean)
- 2.14 (Example: equality of structures): algebra formalized in [algebra.group](algebra/group.hlean).
- 2.15 (Universal properties): in the corresponding file in the [types](types/types.md) folder.

Chapter 3: Sets and logic
---------

- 3.1 (Sets and n-types): [init.trunc](init/trunc.hlean). Example 3.1.9 in [types.univ](types/univ.hlean)
- 3.2 (Propositions as types?): [types.univ](types/univ.hlean)
- 3.3 (Mere propositions): [init.trunc](init/trunc.hlean) and [prop_trunc](prop_trunc.hlean) (Lemma 3.3.5).
- 3.4 (Classical vs. intuitionistic logic): decidable is defined in [init.logic](init/logic.hlean)
- 3.5 (Subsets and propositional resizing): Lemma 3.5.1 is subtype_eq in [types.sigma](types/sigma.hlean), we don't have propositional resizing as axiom yet.
- 3.6 (The logic of mere propositions): in the corresponding file in the [types](types/types.md) folder. (is_trunc_prod is defined in [types.sigma](types/sigma.hlean))
- 3.7 (Propositional truncation): [init.hit](init/hit.hlean) and [hit.trunc](hit/trunc.hlean)
- 3.8 (The axiom of choice): [choice](choice.hlean)
- 3.9 (The principle of unique choice): Lemma 9.3.1 in [hit.trunc](hit/trunc.hlean), Lemma 9.3.2 in [types.trunc](types/trunc.hlean)
- 3.10 (When are propositions truncated?): no formalizable content
- 3.11 (Contractibility): [init.trunc](init/trunc.hlean) (mostly), [types.pi](types/pi.hlean) (Lemma 3.11.6), [types.trunc](types/trunc.hlean) (Lemma 3.11.7), [types.sigma](types/sigma.hlean) (Lemma 3.11.9)

Chapter 4: Equivalences
---------

- 4.1 (Quasi-inverses): not formalized
- 4.2 (Half adjoint equivalences): [init.equiv](init/equiv.hlean) and [types.equiv](types/equiv.hlean)
- 4.3 (Bi-invertible maps): [function](function.hlean) ("biinv f" is "is_retraction f × is_section f")
- 4.4 (Contractible fibers): [types.equiv](types/equiv.hlean)
- 4.5 (On the definition of equivalences): no formalizable content
- 4.6 (Surjections and embeddings): [function](function.hlean)
- 4.7 (Closure properties of equivalences): 4.7.1 in [init.equiv](init/equiv.hlean); 4.7.2 in [function](function.hlean); 4.7.5 and 4.7.7 in [types.sigma](types/sigma.hlean) (sigma_functor is a generalization of total(f)); and 4.7.6 in 4.7.6 in [types.fiber](types/fiber.hlean).
- 4.8 (The object classifier): 4.8.1 and 4.8.2 in [types.fiber](types/fiber.hlean); 4.8.3 and 4.8.4 in [types.univ](types/univ.hlean)
- 4.9 (Univalence implies function extensionality): [init.funext](init/funext.hlean)

Chapter 5: Induction
---------

- 5.1 (Introduction to inductive types): not formalized
- 5.2 (Uniqueness of inductive types): no formalizable content
- 5.3 (W-types): [types.W](types/W.hlean) defines W-types.
- 5.4 (Inductive types are initial algebras): not formalized
- 5.5 (Homotopy-inductive types): not formalized
- 5.6 (The general syntax of inductive definitions): no formalizable content
- 5.7 (Generalizations of inductive types): no formalizable content. Lean has inductive families and mutual induction, but no induction-induction or induction-recursion
- 5.8 (Identity types and identity systems): 5.8.1-5.8.4 not formalized, 5.8.5 in [init.ua](init/ua.hlean) and 5.8.6 in [init.funext](init/funext.hlean)

Chapter 6: Higher inductive types
---------

- 6.1 (Introduction): no formalizable content
- 6.2 (Induction principles and dependent paths): dependent paths in [init.pathover](init/pathover.hlean), circle in [homotopy.circle](homotopy/circle.hlean)
- 6.3 (The interval): [homotopy.interval](homotopy/interval.hlean)
- 6.4 (Circles and spheres): [homotopy.sphere](homotopy/sphere.hlean) and [homotopy.circle](homotopy/circle.hlean)
- 6.5 (Suspensions): [homotopy.suspension](homotopy/susp.hlean) (we define the circle to be the suspension of bool, but Lemma 6.5.1 is similar to proving the ordinary induction principle for the circle in [homotopy.circle](homotopy/circle.hlean)) and a bit in [homotopy.sphere](homotopy/sphere.hlean) and [types.pointed](types/pointed.hlean)
- 6.6 (Cell complexes): we define the torus using the quotient, see [hit.two_quotient](hit/two_quotient.hlean) and [homotopy.torus](homotopy/torus.hlean) (no dependent eliminator defined yet)
- 6.7 (Hubs and spokes): [hit.two_quotient](hit/two_quotient.hlean) and [homotopy.torus](homotopy/torus.hlean) (no dependent eliminator defined yet)
- 6.8 (Pushouts): [hit.pushout](hit/pushout.hlean). Some of the "standard homotopy-theoretic constructions" have separate files, although not all of them have been defined explicitly yet
- 6.9 (Truncations): [hit.trunc](hit/trunc.hlean) (except Lemma 6.9.3)
- 6.10 (Quotients): [hit.set_quotient](hit/set_quotient.hlean) (up to 6.10.3). We define integers differently, to make them compute, in the folder [types.int](types/int/int.md). 6.10.13 is in [types.int.hott](types/int/hott.hlean)
- 6.11 (Algebra): [algebra.group](algebra/group.hlean), [algebra.homotopy_group](algebra/homotopy_group.hlean)
- 6.12 (The flattening lemma): [hit.quotient](hit/quotient.hlean) (for quotients instead of homotopy coequalizers, but these are practically the same)
- 6.13 (The general syntax of higher inductive definitions): no formalizable content

Chapter 7: Homotopy n-types
---------

- 7.1 (Definition of n-types): [init.trunc](init/trunc.hlean), [types.trunc](types/trunc.hlean), [types.sigma](types/sigma.hlean) (Theorem 7.1.8), [types.pi](types/pi.hlean) (Theorem 7.1.9), [prop_trunc](prop_trunc.hlean) (Theorem 7.1.10)
- 7.2 (Uniqueness of identity proofs and Hedberg’s theorem): [init.hedberg](init/hedberg.hlean) and [types.trunc](types/trunc.hlean)
- 7.3 (Truncations): [init.hit](init/hit.hlean), [hit.trunc](hit/trunc.hlean) and [types.trunc](types/trunc.hlean)
- 7.4 (Colimits of n-types): not formalized
- 7.5 (Connectedness): [homotopy.connectedness](homotopy/connectedness.hlean) (the main "induction principle" Lemma 7.5.7)
- 7.6 (Orthogonal factorization): not formalized
- 7.7 (Modalities): not formalized, and may be unformalizable in general because it's unclear how to define modalities

Chapter 8: Homotopy theory
---------

Unless otherwise noted, the files are in the folder [homotopy](homotopy/homotopy.md)

- 8.1 (π_1(S^1)): [homotopy.circle](homotopy/circle.hlean) (only the encode-decode proof)
- 8.2 (Connectedness of suspensions): [homotopy.connectedness](homotopy/connectedness.hlean) (different proof)
- 8.3 (πk≤n of an n-connected space and π_{k<n}(S^n)): [homotopy.homotopy_group](homotopy/homotopy_group.hlean)
- 8.4 (Fiber sequences and the long exact sequence): not formalized
- 8.5 (The Hopf fibration): [homotopy.circle](homotopy/circle.hlean) (H-space structure on the circle, Lemma 8.5.8), [homotopy.join](homotopy/join.hlean) (join is associative, Lemma 8.5.9), the rest is not formalized
- 8.6 (The Freudenthal suspension theorem): [homotopy.connectedness](homotopy/connectedness.hlean) (Lemma 8.6.1), [homotopy.wedge](homotopy/wedge.hlean) (Wedge connectivity, Lemma 8.6.2), the rest is not formalized
- 8.7 (The van Kampen theorem): not formalized
- 8.8 (Whitehead’s theorem and Whitehead’s principle): not formalized
- 8.9 (A general statement of the encode-decode method): not formalized
- 8.10 (Additional Results): not formalized

Chapter 9: Category theory
---------

Every file is in the folder [algebra.category](algebra/category/category.md)

- 9.1 (Categories and precategories): [precategory](algebra/category/precategory.hlean), [iso](algebra/category/iso.hlean), [category](algebra/category/category.hlean), [groupoid](algebra/category/groupoid.hlean) (mostly)
- 9.2 (Functors and transformations): [functor.basic](algebra/category/functor/basic.hlean), [nat_trans](algebra/category/nat_trans.hlean), [constructions.functor](algebra/category/constructions/functor.hlean)
- 9.3 (Adjunctions): [functor.adjoint](algebra/category/functor/adjoint.hlean)
- 9.4 (Equivalences): [functor.equivalence](algebra/category/functor/equivalence.hlean) and [functor.attributes](algebra/category/functor/attributes.hlean) (partially)
- 9.5 (The Yoneda lemma): [constructions.opposite](algebra/category/constructions/opposite.hlean), [constructions.product](algebra/category/constructions/product.hlean), [functor.yoneda](algebra/category/functor/yoneda.hlean) (up to Theorem 9.5.9)
- 9.6 (Strict categories): [strict](algebra/category/strict.hlean) (only definition)
- 9.7 (†-categories): not formalized
- 9.8 (The structure identity principle): not formalized
- 9.9 (The Rezk completion): not formalized

Chapter 10: Set theory
----------

Not formalized, and parts may be unformalizable because Lean lacks induction-recursion.


Chapter 11: Real numbers
----------

- 11.1 (The field of rational numbers): To be ported from the standard library.

The rest is not formalized, and parts may be unformalizable because Lean lacks induction-induction
