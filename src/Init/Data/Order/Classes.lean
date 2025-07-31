/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core

namespace Std

/-!
# Order-related typeclasses

This module provides the typeclasses used to state that basic operations on some type `α`
reflect a certain well-behaved order structure on `α`.

The basic operations are provided by typeclasses such as `LE α`, `LT α`, `Ord α` or `Min α`.
All of them describe at least some way to compare elements in `α`. Usually, any subset of them
is available and can show (or needs) that these comparisons are well-behaved in some sense.

For example, one could merely require that the available operations reflect a preorder
(where the less-or-equal relation only needs to be reflexive and transitive). Alternatively,
one could require a full linear order (additionally requiring antisymmetry and totality of the
less-or-equal relation).

In order to be independent from the actually available set of basic operations, these lawfulness
properties are stated for a separate typeclass `OrderData α`. See the docstring of
`OrderData` for a more detailed explanation for its necessity.
-/

/--
This data-carrying typeclass defines which elements of `α` are less, and less or equal, to
which other elements.

The operations of this class are not meant to be used directly.
Instead users should rely on typeclasses such as `LE α`, `LT α` or `Ord α` that provide basic
operations, here `<`, `>` and `compare`.

**Role of `OrderData α`:**

This typeclass allows to describe order-related properties of `α` is an abstract, canonical way,
no matter which basic operations are available on `α`.

For example, there are different ways to say that the order on `α` is a linear order, depending
on the available operations:

* `(· ≤ ·)` is a reflexive, transitive, antisymmetric and total order.
* `(· ≤ ·)` is antisymmetric, `a < b ↔ ¬ b ≤ a` and `(· < ·)` is irreflexive, transitive and asymmetric.
* `min a b` is either `a` or `b`, is symmetric and satisfies the
  following property: `min c (min a b) = c` if and only if `min c a = c` and `min c b = c`.

These diverse formulations are confusing and make it harder to compose theorems that rely on
different sets of requirements, even if they all assume a linear order after  all.

The solution is to state all of these properties in terms of `OrderData α`. For example:

```lean
theorem le_antisymm {α : Type u} [OrderData α] [LE α]
    [PartialOrder α] -- The order on `α` induced by `OrderData α` is, among other things, antisymmetric.
    [LawfulOrderLE α] -- `≤` is the less-or-equal relation induced by `OrderData α`.
    {a b : α} : a ≤ b → b ≤ a → a = b := by
  sorry
```

**Limitations:**

Some rare situations are not representable by an `OrderData α` instance. For example, every
`Ord α` instance that is compatible with `OrderData α` must satisfy the equation
`compare a b = (compare b a).swap`, and every `LT α` instance that is compatible with
`OrderData α` must be asymmetric (`a < b` and `b < a` are mutually exclusive).

In such situations, there are two alternatives:

* Resort to elementary axiomatic typeclasses such as `Std.Irrefl` or `Std.Antisymm`.
* Alternatively, do not use `LE α`, `LT α` or other order-related classes at all. Instead,
  introduce a new typeclass that better conveys the unusual semantics that are desired.
-/
public class OrderData (α : Type u) where
  IsLE : α → α → Prop

/--
This typeclass states that the order structure on `α`, represented by an `OrderData α` instance,
is a preorder. In other words, the less-or-equal relation is reflexive and transitive.
-/
public class Preorder (α : Type u) [OrderData α] where
  le_refl : ∀ a : α, OrderData.IsLE a a
  le_trans : ∀ a b c : α, OrderData.IsLE a b → OrderData.IsLE b c → OrderData.IsLE a c

/--
This typeclass states that the order structure on `α`, represented by an `OrderData α` instance,
is a partial order.
In other words, the less-or-equal relation is reflexive, transitive and antisymmetric.
-/
public class PartialOrder (α : Type u) [OrderData α] extends Preorder α where
  le_antisymm : ∀ a b : α, OrderData.IsLE a b → OrderData.IsLE b a → a = b

/--
This typeclass states that the order structure on `α`, represented by an `OrderData α` instance,
is a linear preorder.
In other words, the less-or-equal relation is reflexive, transitive and total.
-/
public class LinearPreorder (α : Type u) [OrderData α] extends Preorder α where
  le_total : ∀ a b : α, OrderData.IsLE a b ∨ OrderData.IsLE b a

/--
This typeclass states that the order structure on `α`, represented by an `OrderData α` instance,
is a linear order.
In other words, the less-or-equal relation is reflexive, transitive, antisymmetric and total.
-/
public class IsLinearOrder (α : Type u) [OrderData α] extends PartialOrder α, LinearPreorder α

section LE

/--
This typeclass states that the synthesized `LE α` instance is compatible with the `OrderData α`
instance. This means that `LE.le` equals `OrderData.IsLE`.
-/
public class LawfulOrderLE (α : Type u) [LE α] [OrderData α] where
  le_iff : ∀ a b : α, a ≤ b ↔ OrderData.IsLE a b

end LE

section LT

/--
This typeclass states that the synthesized `LT α` instance is compatible with the `OrderData α`
instance. This means that `LT.lt a b` holds if and only if `a` is less or equal to `b` according
to the `OrderData α` instance, but `b` is not less or equal to `a`.

`LawfulOrderLT α` automatically entails that `LT α` is asymmetric: `a < b` and `b < a` can never
be true simultaneously.

`LT α` does not uniquely determine the `OrderData α`: There can be only one compatible order data
instance that is total, but there can be others that are not total.
-/
public class LawfulOrderLT (α : Type u) [LT α] [OrderData α] where
  lt_iff : ∀ a b : α, a < b ↔ OrderData.IsLE a b ∧ ¬ OrderData.IsLE b a

end LT

section Min

/--
This typeclass states that `Min.min a b` returns one of its arguments, either `a` or `b`.
-/
public class MinEqOr (α : Type u) [Min α] where
  min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b

/--
This typeclass states that being less or equal to `Min.min a b` is equivalent to being less or
equal to both `a` and `b`, according to the synthesized `OrderData α` instance.
-/
public class LawfulOrderInf (α : Type u) [Min α] [OrderData α] where
  le_min_iff : ∀ a b c : α, OrderData.IsLE a (min b c) ↔ OrderData.IsLE a b ∧ OrderData.IsLE a c

/--
This typeclass bundles `MinEqOr α` and `LawfulOrderInf α`. It characterizes when a `Min α`
instance reasonably computes minima in some type `α` that has an `OrderData α` instance.

As long as `α` is a preorder (see `Preorder α`), this typeclass implies that the order on
`α` is total and that `Min.min a b` returns either `a` or `b`, whichever is less or equal to
the other.
-/
public class LawfulOrderMin (α : Type u) [Min α] [OrderData α] extends MinEqOr α, LawfulOrderInf α

end Min

section Max

/--
This typeclass states that `Max.max a b` returns one of its arguments, either `a` or `b`.
-/
public class MaxEqOr (α : Type u) [Max α] where
  max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b

/--
This typeclass states that being less or equal to `Max.max a b` is equivalent to being less or
equal to both `a` and `b`, according to the synthesized `OrderData α` instance.
-/
public class LawfulOrderSup (α : Type u) [Max α] [OrderData α] where
  max_le_iff : ∀ a b c : α, OrderData.IsLE (max a b) c ↔ OrderData.IsLE a c ∧ OrderData.IsLE b c

/--
This typeclass bundles `MaxEqOr α` and `LawfulOrderSup α`. It characterizes when a `Max α`
instance reasonably computes maxima in some type `α` that has an `OrderData α` instance.

As long as `α` is a preorder (see `Preorder α`), this typeclass implies that the order on
`α` is total and that `Min.min a b` returns either `a` or `b`, whichever is greater or equal to
the other.
-/
public class LawfulOrderMax (α : Type u) [Max α] [OrderData α] extends MaxEqOr α, LawfulOrderSup α

end Max

end Std
