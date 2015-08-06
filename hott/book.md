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
| Ch 3  | + | - | + | + | ½ | + | + | - | ½ | .  | +  |    |    |    |    |
| Ch 4  | - | + | - | + | . | + | - | - | + |    |    |    |    |    |    |
| Ch 5  | - | . | - | - | - | . | . | ½ |   |    |    |    |    |    |    |
| Ch 6  | . | + | + | + | + | ½ | ½ | ¼ | ¼ | ¼  | ¾  | -  | .  |    |    |
| Ch 7  | + | + | + | - | - | - | - |   |   |    |    |    |    |    |    |
| Ch 8  | ¾ | - | - | - | - | - | - | - | - | -  |    |    |    |    |    |
| Ch 9  | ¾ | + | ¼ | ¼ | ½ | ½ | - | - | - |    |    |    |    |    |    |
| Ch 10 | - | - | - | - | - |   |   |   |   |    |    |    |    |    |    |
| Ch 11 | - | - | - | - | - | - |   |   |   |    |    |    |    |    |    |

Things not in the book:

* One major difference is that in this library we heavily use pathovers, so we need less theorems about transports, but instead corresponding theorems about pathovers. These are in [init.pathover](init/pathover.hlean). For higher paths there are [squares](cubical/square.hlean), [squareovers](cubical/squareover.hlean), and the rudiments of [cubes](cubical/cube.hlean) and [cubeovers](cubical/cubeover.hlean).

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
- 2.9 (Π-types and the function extensionality axiom): [init.funext](init/funext.hlean) and [types.pi](types/pi.hlean)
- 2.10 (Universes and the univalence axiom): [init.ua](init/ua.hlean)
- 2.11 (Identity type): [init.equiv](init/equiv.hlean) (ap is equivalence), [types.eq](types/eq.hlean) and [cubical.square](cubical/square.hlean) (characterization of pathovers in equality types)
- 2.12 (Coproducts): [types.sum](types/sum.hlean)
- 2.13 (Natural numbers): [types.nat.hott](types/nat/hott.hlean)
- 2.14 (Example: equality of structures): algebra formalized in [algebra.group](algebra/group.hlean).
- 2.15 (Universal properties): in the corresponding file in the [types](types/types.md) folder.

Chapter 3: Sets and logic
---------

- 3.1 (Sets and n-types): [init.trunc](init/trunc.hlean)
- 3.2 (Propositions as types?): not formalized
- 3.3 (Mere propositions): [init.trunc](init/trunc.hlean) and [hprop_trunc](hprop_trunc.hlean) (Lemma 3.3.5).
- 3.4 (Classical vs. intuitionistic logic): decidable is defined in [init.logic](init/logic.hlean)
- 3.5 (Subsets and propositional resizing): Lemma 3.5.1 is subtype_eq in [types.sigma](types/sigma.hlean), we don't have propositional resizing as axiom yet.
- 3.6 (The logic of mere propositions): in the corresponding file in the [types](types/types.md) folder. (is_trunc_prod is defined in [types.sigma](types/sigma.hlean))
- 3.7 (Propositional truncation): [init.hit](init/hit.hlean) and [hit.trunc](hit/trunc.hlean)
- 3.8 (The axiom of choice): not formalized
- 3.9 (The principle of unique choice): Lemma 9.3.1 is equiv_trunc in [hit.trunc](hit/trunc.hlean), Lemma 9.3.2 is not formalized
- 3.10 (When are propositions truncated?): no formalizable content
- 3.11 (Contractibility): [init.trunc](init/trunc.hlean) (mostly), [types.pi](types/pi.hlean) (Lemma 3.11.6), [types.trunc](types/trunc.hlean) (Lemma 3.11.7), [types.sigma](types/sigma.hlean) (Lemma 3.11.9) 

Chapter 4: Equivalences
---------

- 4.1 (Quasi-inverses): not formalized
- 4.2 (Half adjoint equivalences): [init.equiv](init/equiv.hlean) and [types.equiv](types/equiv.hlean)
- 4.3 (Bi-invertible maps): not formalized
- 4.4 (Contractible fibers): [types.equiv](types/equiv.hlean)
- 4.5 (On the definition of equivalences): no formalizable content
- 4.6 (Surjections and embeddings): [function](function.hlean)
- 4.7 (Closure properties of equivalences): not formalized
- 4.8 (The object classifier): not formalized
- 4.9 (Univalence implies function extensionality): [init.funext](init/funext.hlean)

Chapter 5: Induction
---------

- 5.1 (Introduction to inductive types): not formalized
- 5.2 (Uniqueness of inductive types): no formalizable content
- 5.3 (W-types): related: [types.W](types/W.hlean)
- 5.4 (Inductive types are initial algebras): not formalized
- 5.5 (Homotopy-inductive types): not formalized
- 5.6 (The general syntax of inductive definitions): no formalizable content
- 5.7 (Generalizations of inductive types): no formalizable content. Lean has inductive families and mutual induction, but no induction-induction or induction-recursion
- 5.8 (Identity types and identity systems): 5.8.1-5.8.4 not formalized, 5.8.5 in [init.ua](init/ua.hlean) and 5.8.6 in [init.funext](init/funext.hlean)

Chapter 6: Higher inductive types
---------

- 6.1 (Introduction): no formalizable content
- 6.2 (Induction principles and dependent paths): dependent paths in [init.pathover](init/pathover.hlean), circle in [hit.circle](hit/circle.hlean)
- 6.3 (The interval): [hit.interval](hit/interval.hlean)
- 6.4 (Circles and spheres): [hit.circle](hit/circle.hlean)
- 6.5 (Suspensions): [hit.suspension](hit/suspension.hlean) (we define the circle to be the suspension of bool, but Lemma 6.5.1 is similar to proving the ordinary induction principle for the circle in [hit.circle](hit/circle.hlean)) and a bit in [hit.sphere](hit/sphere.hlean) and [types.pointed](types/pointed.hlean)
- 6.6 (Cell complexes): we define the torus using the quotient, see [hit.two_quotient](hit/two_quotient.hlean) and [hit.torus](hit/torus.hlean) (no dependent eliminator defined yet)
- 6.7 (Hubs and spokes): [hit.two_quotient](hit/two_quotient.hlean) and [hit.torus](hit/torus.hlean) (no dependent eliminator defined yet)
- 6.8 (Pushouts): [hit.pushout](hit/pushout.hlean) (not everything yet)
- 6.9 (Truncations): [hit.trunc](hit/trunc.hlean) (not everything yet)
- 6.10 (Quotients): [hit.set_quotient](hit/set_quotient.hlean), [types.int](types/int/int.md) (folder) (not everything yet)
- 6.11 (Algebra): [algebra.group](algebra/group.hlean), [algebra.fundamental_group](algebra/fundamental_group.hlean) (no homotopy groups yet)
- 6.12 (The flattening lemma): not formalized yet
- 6.13 (The general syntax of higher inductive definitions): no formalizable content

Chapter 7: Homotopy n-types
---------

- 7.1 (Definition of n-types): [init.trunc](init/trunc.hlean), [types.trunc](types/trunc.hlean), [types.sigma](types/sigma.hlean) (Theorem 7.1.8), [types.pi](types/pi.hlean) (Theorem 7.1.9), [hprop_trunc](hprop_trunc.hlean) (Theorem 7.1.10)
- 7.2 (Uniqueness of identity proofs and Hedberg’s theorem): [init.hedberg](init/hedberg.hlean) and [types.trunc](types/trunc.hlean)
- 7.3 (Truncations): [init.hit](init/hit.hlean), [hit.trunc](hit/trunc.hlean) and [types.trunc](types/trunc.hlean)
- 7.4 (Colimits of n-types): not formalized
- 7.5 (Connectedness): not formalized
- 7.6 (Orthogonal factorization): not formalized 
- 7.7 (Modalities): not formalized, and may be unformalizable in general because it's unclear how to define modalities

Chapter 8: Homotopy theory
---------

- 8.1 (π_1(S^1)): [hit.circle](hit/circle.hlean) (only one of the proofs)
- 8.2 (Connectedness of suspensions): not formalized
- 8.3 (πk≤n of an n-connected space and π_{k<n}(S^n)): not formalized
- 8.4 (Fiber sequences and the long exact sequence): not formalized 
- 8.5 (The Hopf fibration): not formalized 
- 8.6 (The Freudenthal suspension theorem): not formalized 
- 8.7 (The van Kampen theorem): not formalized 
- 8.8 (Whitehead’s theorem and Whitehead’s principle): not formalized 
- 8.9 (A general statement of the encode-decode method): not formalized 
- 8.10 (Additional Results): not formalized 

Chapter 9: Category theory
---------

Every file is in the folder [algebra.category](algebra/category/category.md)

- 9.1 (Categories and precategories): [precategory](algebra/category/precategory.hlean), [iso](algebra/category/iso.hlean), [category](algebra/category/category.hlean), [groupoid](algebra/category/groupoid.hlean) (mostly)
- 9.2 (Functors and transformations): [functor](algebra/category/functor.hlean), [nat_trans](algebra/category/nat_trans.hlean), [constructions.functor](algebra/category/constructions/functor.hlean)
- 9.3 (Adjunctions): [adjoint](algebra/category/adjoint.hlean) (only definition)
- 9.4 (Equivalences): [adjoint](algebra/category/adjoint.hlean) (only definitions)
- 9.5 (The Yoneda lemma): [constructions.opposite](algebra/category/constructions/opposite.hlean), [constructions.product](algebra/category/constructions/product.hlean), [yoneda](algebra/category/yoneda.hlean) (up to definition of Yoneda embedding)
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
