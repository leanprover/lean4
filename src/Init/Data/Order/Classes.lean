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

The basic operations are provided by the typeclasses `LE α`, `LT α`, `BEq α`, `Ord α`, `Min α` and
`Max α`.
All of them describe at least some way to compare elements in `α`. Usually, any subset of them
is available and one can/must show that these comparisons are well-behaved in some sense.

For example, one could merely require that the available operations reflect a preorder
(where the less-or-equal relation only needs to be reflexive and transitive). Alternatively,
one could require a full linear order (additionally requiring antisymmetry and totality of the
less-or-equal relation).

There are many ways to characterize, say, linear orders:

* `(· ≤ ·)` is reflexive, transitive, antisymmetric and total.
* `(· ≤ ·)` is antisymmetric, `a < b ↔ ¬ b ≤ a` and `(· < ·)` is irreflexive, transitive and asymmetric.
* `min a b` is either `a` or `b`, is symmetric and satisfies the
  following property: `min c (min a b) = c` if and only if `min c a = c` and `min c b = c`.

It is desirable that lemmas about linear orders state this hypothesis in a canonical way.
Therefore, the classes defining preorders, partial orders, linear preorders and linear orders
are all formulated purely in terms of `LE`. For other operations, there are
classes for compatibility of `LE` with other operations. Hence, a lemma may look like:

```lean
theorem lt_trans {α : Type u} [LE α] [LT α]
    [IsPreorder α] -- The order on `α` induced by `LE α` is, among other things, transitive.
    [LawfulOrderLT α] -- `<` is the less-than relation induced by `LE α`.
    {a b : α} : a < b → b < c → a < c := by
  sorry
```
-/

/--
This typeclass states that the order structure on `α`, represented by an `LE α` instance,
is a preorder. In other words, the less-or-equal relation is reflexive and transitive.
-/
public class IsPreorder (α : Type u) [LE α] where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

/--
This typeclass states that the order structure on `α`, represented by an `LE α` instance,
is a partial order.
In other words, the less-or-equal relation is reflexive, transitive and antisymmetric.
-/
public class IsPartialOrder (α : Type u) [LE α] extends IsPreorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

/--
This typeclass states that the order structure on `α`, represented by an `LE α` instance,
is a linear preorder.
In other words, the less-or-equal relation is reflexive, transitive and total.
-/
public class IsLinearPreorder (α : Type u) [LE α] extends IsPreorder α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a

/--
This typeclass states that the order structure on `α`, represented by an `LE α` instance,
is a linear order.
In other words, the less-or-equal relation is reflexive, transitive, antisymmetric and total.
-/
public class IsLinearOrder (α : Type u) [LE α] extends IsPartialOrder α, IsLinearPreorder α

section LT

/--
This typeclass states that the synthesized `LT α` instance is compatible with the `LE α`
instance. This means that `LT.lt a b` holds if and only if `a` is less or equal to `b` according
to the `LE α` instance, but `b` is not less or equal to `a`.

`LawfulOrderLT α` automatically entails that `LT α` is asymmetric: `a < b` and `b < a` can never
be true simultaneously.

`LT α` does not uniquely determine the `LE α`: There can be only one compatible order data
instance that is total, but there can be others that are not total.
-/
public class LawfulOrderLT (α : Type u) [LT α] [LE α] where
  lt_iff : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a

end LT

section BEq

public class LawfulOrderBEq (α : Type u) [BEq α] [LE α] where
  beq_iff_le_and_ge : ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a

end BEq

section Min

/--
This typeclass states that `Min.min a b` returns one of its arguments, either `a` or `b`.
-/
public class MinEqOr (α : Type u) [Min α] where
  min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b

/--
If both `a` and `b` satisfy some property `P`, then so does `min a b`, because it is equal to
either `a` or `b`.
-/
public theorem MinEqOr.elim {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    P (min a b) := by
  cases MinEqOr.min_eq_or a b <;> rename_i h
  case inl => exact h.symm ▸ ha
  case inr => exact h.symm ▸ hb

/--
This typeclass states that being less or equal to `min a b` is equivalent to being less or
equal to both `a` and `b`..
-/
public class LawfulOrderInf (α : Type u) [Min α] [LE α] where
  le_min_iff : ∀ a b c : α, a ≤ (min b c) ↔ a ≤ b ∧ a ≤ c

/--
This typeclass bundles `MinEqOr α` and `LawfulOrderInf α`. It characterizes when a `Min α`
instance reasonably computes minima in some type `α` that has an `LE α` instance.

As long as `α` is a preorder (see `IsPreorder α`), this typeclass implies that the order on
`α` is total and that `Min.min a b` returns either `a` or `b`, whichever is less or equal to
the other.
-/
public class LawfulOrderMin (α : Type u) [Min α] [LE α] extends MinEqOr α, LawfulOrderInf α

/--
This typeclass states that `min a b = if a ≤ b then a else b` (for any `DecidableLE α` instance).
-/
public class LawfulOrderLeftLeaningMin (α : Type u) [Min α] [LE α] where
  min_eq_left : ∀ a b : α, a ≤ b → min a b = a
  min_eq_right : ∀ a b : α, ¬ a ≤ b → min a b = b

end Min

section Max

/--
This typeclass states that `Max.max a b` returns one of its arguments, either `a` or `b`.
-/
public class MaxEqOr (α : Type u) [Max α] where
  max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b

/--
If both `a` and `b` satisfy some property `P`, then so does `max a b`, because it is equal to
either `a` or `b`.
-/
public theorem MaxEqOr.elim {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    P (max a b) := by
  cases MaxEqOr.max_eq_or a b <;> rename_i h
  case inl => exact h.symm ▸ ha
  case inr => exact h.symm ▸ hb

/--
This typeclass states that being less or equal to `Max.max a b` is equivalent to being less or
equal to both `a` and `b`.
-/
public class LawfulOrderSup (α : Type u) [Max α] [LE α] where
  max_le_iff : ∀ a b c : α, (max a b) ≤ c ↔ a ≤ c ∧ b ≤ c

/--
This typeclass bundles `MaxEqOr α` and `LawfulOrderSup α`. It characterizes when a `Max α`
instance reasonably computes maxima in some type `α` that has an `LE α` instance.

As long as `α` is a preorder (see `IsPreorder α`), this typeclass implies that the order on
`α` is total and that `Min.min a b` returns either `a` or `b`, whichever is greater or equal to
the other.
-/
public class LawfulOrderMax (α : Type u) [Max α] [LE α] extends MaxEqOr α, LawfulOrderSup α

/--
This typeclass states that `max a b = if b ≤ a then a else b` (for any `DecidableLE α` instance).
-/
public class LawfulOrderLeftLeaningMax (α : Type u) [Max α] [LE α] where
  max_eq_left : ∀ a b : α, b ≤ a → max a b = a
  max_eq_right : ∀ a b : α, ¬ b ≤ a → max a b = b

end Max

end Std
