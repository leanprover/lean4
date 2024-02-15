/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
prelude
import Init.Data.Int.Basic

/-!
# `NatCast` and `IntCast`

We introduce the typeclass `NatCast R` for a type `R` with a "canonical homomorphism" `Nat → R`.
The typeclass carries the data of the function, but no required axioms.

This typeclass was introduced to support a uniform `simp` normal form for such morphisms.

Without such a typeclass, we would have coercions such as `Int.ofNat`,
but also later in Mathlib the generic coercion from `Nat` into any semiring (including `Int`),
and we would need to use `simp` to move between them.
However `simp` lemmas expressed using a non-normal form on the LHS would then not fire.

In order to avoid this, we introduce this typeclass as early as possible,
ensure it is a higher priority coercion that built-in coercions such as `Int.ofNat`,
and write all of our simp lemmas in terms of it.

Typically different instances of this class for the same target type `R` are definitionally equal,
and so differences in the instance do not block `simp` or `rw`.

The same discussion applied to `Int`, so we also introduce `IntCast`.

## Note about coercions into arbitrary types:

Coercions such as `Nat.cast` that go from a concrete structure such as
`Nat` to an arbitrary type `R` should be set up as follows:
```lean
instance : CoeTail Nat R where coe := ...
instance : CoeHTCT Nat R where coe := ...
```

It needs to be `CoeTail` instead of `Coe` because otherwise type-class
inference would loop when constructing the transitive coercion `Nat → Nat → Nat → ...`.
Sometimes we also need to declare the `CoeHTCT` instance
if we need to shadow another coercion
(e.g. `Nat.cast` should be used over `Int.ofNat`).

-/

/-- Type class for the canonical homomorphism `Nat → R`. -/
class NatCast (R : Type u) where
  /-- The canonical map `Nat → R`. -/
  protected natCast : Nat → R

instance : NatCast Nat where natCast n := n
instance : NatCast Int where natCast n := Int.ofNat n

/--
Canonical homomorphism from `Nat` to a type `R`.

It contains just the function, with no axioms.
In practice, the target type will likely have a (semi)ring structure,
and this homomorphism should be a ring homomorphism.

The prototypical example is `Int.ofNat`.

This class and `IntCast` exist to allow different libraries with their own types that can be notated as natural numbers to have consistent `simp` normal forms without needing to create coercion simplification sets that are aware of all combinations. Libraries should make it easy to work with `NatCast` where possible. For instance, in Mathlib there will be such a homomorphism (and thus a `NatCast R` instance) whenever `R` is an additive monoid with a `1`.
-/
@[coe, reducible, match_pattern] protected def Nat.cast {R : Type u} [NatCast R] : Nat → R :=
  NatCast.natCast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [NatCast R] : CoeTail Nat R where coe := Nat.cast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [NatCast R] : CoeHTCT Nat R where coe := Nat.cast

/-- This instance is needed to ensure that `instCoeNatInt` is not used. -/
instance : Coe Nat Int where coe := Nat.cast

/--
The canonical homomorphism `Int → R`.
In most use cases `R` will have a ring structure and this will be a ring homomorphism.
-/
class IntCast (R : Type u) where
  /-- The canonical map `Int → R`. -/
  protected intCast : Int → R

instance : IntCast Int where intCast n := n

/--
Apply the canonical homomorphism from `Int` to a type `R` from an `IntCast R` instance.

The prototypical example is `Int.ofNat`.

In Mathlib there will be such a homomorphism whenever `R` is an additive group with a `1`.
-/
@[coe, reducible, match_pattern] protected def Int.cast {R : Type u} [IntCast R] : Int → R :=
  IntCast.intCast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [IntCast R] : CoeTail Int R where coe := Int.cast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [IntCast R] : CoeHTCT Int R where coe := Int.cast
