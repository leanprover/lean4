module

prelude
public import Init.Data.Order.Classes
import Init.SimpLemmas

namespace Std

/-!
This module provides utilities for the creation of order-related typeclass instances.
-/

/--
Creates an `OrderData α` instance from an `LE α` instance.

As `OrderData α` captures the same information as `LE α`, this is possible without restriction
or loss of information.
-/
public def OrderData.ofLE (α : Type u) [LE α] : OrderData α where
  IsLE := LE.le

/--
The `OrderData α` instance obtained from an `LE α` instance is compatible with said `LE α` instance.
-/
public instance OrderData.instLawfulOrderLEOfLE {α : Type u} [LE α] :
    haveI := OrderData.ofLE α
    LawfulOrderLE α :=
  letI := OrderData.ofLE α
  { le_iff _ _ := by exact Iff.rfl }

/--
If an `OrderData α` instance is compatible with an `LE α` instance that is reflexive, antisymmetric,
transitive and total, then the `OrderData α` instance is a linear order.
-/
public theorem LinearOrder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
    (le_refl : ∀ a : α, a ≤ a)
    (le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    LinearOrder α where
  le_refl := by simpa [LawfulOrderLE.le_iff] using le_refl
  le_antisymm := by simpa [LawfulOrderLE.le_iff] using le_antisymm
  le_trans := by simpa [LawfulOrderLE.le_iff] using le_trans
  le_total := by simpa [LawfulOrderLE.le_iff] using le_total

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma characterizes
in terms of `LE α` when a `Min α` instance "behaves like an infimum operator".
-/
public theorem LawfulOrderInf.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (le_min_iff : ∀ a b c : α, a ≤ Min.min b c ↔ a ≤ b ∧ a ≤ c) : LawfulOrderInf α where
  le_min_iff := by simpa [LawfulOrderLE.le_iff] using le_min_iff

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma derives
a `MinEqOr α` instance from a property involving `LE α` and `Min α` instances.
-/
public theorem MinEqOr.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) : MinEqOr α where
  min_eq_or := by simpa [LawfulOrderLE.le_iff] using min_eq_or

/--
Returns a `LawfulOrderMin α` instance given certain properties.

If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma derives
a `LawfulOrderMin α` instance from two properties involving `LE α` and `Min α` instances.

This convenience lemma combines `LawfulOrderInf.ofLE` and `LawfulOrderMin.ofLE`.
-/
public theorem LawfulOrderMin.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (le_min_iff : ∀ a b c : α, a ≤ Min.min b c ↔ a ≤ b ∧ a ≤ c)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) : LawfulOrderMin α where
  toLawfulOrderInf := .ofLE le_min_iff
  toMinEqOr := .ofLE min_eq_or

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma characterizes
in terms of `LE α` when a `Max α` instance "behaves like an supremum operator".
-/
public def LawfulOrderSup.ofLE {α : Type u} [OrderData α] [Max α] [LE α] [LawfulOrderLE α]
    (max_le_iff : ∀ a b c : α, Max.max a b ≤ c ↔ a ≤ c ∧ b ≤ c) : LawfulOrderSup α where
  max_le_iff := by simpa [LawfulOrderLE.le_iff] using max_le_iff

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma derives
a `MaxEqOr α` instance from a property involving `LE α` and `Max α` instances.
-/
public def MaxEqOr.ofLE {α : Type u} [OrderData α] [Max α] [LE α] [LawfulOrderLE α]
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) : MaxEqOr α where
  max_eq_or := by simpa [LawfulOrderLE.le_iff] using max_eq_or

/--
Returns a `LawfulOrderMax α` instance given certain properties.

If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma derives
a `LawfulOrderMax α` instance from two properties involving `LE α` and `Max α` instances.

This convenience lemma combines `LawfulOrderSup.ofLE` and `LawfulOrderMax.ofLE`.
-/
public def LawfulOrderMax.ofLE {α : Type u} [OrderData α] [Max α] [LE α] [LawfulOrderLE α]
    (max_le_iff : ∀ a b c : α, Max.max a b ≤ c ↔ a ≤ c ∧ b ≤ c)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) : LawfulOrderMax α where
  toLawfulOrderSup := .ofLE max_le_iff
  toMaxEqOr := .ofLE max_eq_or

end Std
