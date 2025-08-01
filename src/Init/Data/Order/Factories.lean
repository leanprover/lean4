/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Classes
import Init.Classical

namespace Std

/-!
This module provides utilities for the creation of order-related typeclass instances.
-/

section OfLE

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
public instance LawfulOrderLE.ofLE {α : Type u} [LE α] :
    haveI := OrderData.ofLE α
    LawfulOrderLE α :=
  letI := OrderData.ofLE α
  { le_iff _ _ := by exact Iff.rfl }

/--
If an `OrderData α` instance is compatible with an `LE α` instance that is reflexive and transitive,
then the `OrderData α` instance is a preorder.
-/
public theorem IsPreorder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
    (le_refl : ∀ a : α, a ≤ a)
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c) :
    IsPreorder α where
  le_refl := by simpa [LawfulOrderLE.le_iff] using le_refl
  le_trans := by simpa [LawfulOrderLE.le_iff] using le_trans

/--
If an `OrderData α` instance is compatible with an `LE α` instance that is transitive and total,
then the `OrderData α` instance is a linear preorder.
-/
public theorem IsLinearPreorder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    IsLinearPreorder α where
  toIsPreorder := .ofLE (by simpa using fun a => le_total a a) le_trans
  le_total := by simpa [LawfulOrderLE.le_iff] using le_total

/--
If an `OrderData α` instance is compatible with an `LE α` instance that is reflexive, antisymmetric
and transitive, then the `OrderData α` instance is a partial order.
-/
public theorem IsPartialOrder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
    (le_refl : ∀ a : α, a ≤ a)
    (le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c) :
    IsPartialOrder α where
  toIsPreorder := .ofLE le_refl le_trans
  le_antisymm := by simpa [LawfulOrderLE.le_iff] using le_antisymm

/--
If an `OrderData α` instance is compatible with an `LE α` instance that is antisymmetric,
transitive and total, then the `OrderData α` instance is a linear order.
-/
public theorem IsLinearOrder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
    (le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    IsLinearOrder α where
  toIsLinearPreorder := .ofLE le_trans le_total
  le_antisymm := by simpa [LawfulOrderLE.le_iff] using le_antisymm

/--
Returns a `LawfulOrderLT α` instance given certain properties.

If an `OrderData α` instance is compatible with an `LT α` instance, then this lemma derives
a `LawfulOrderMin α` instance from two properties involving `LE α` and `Min α` instances.

This convenience lemma combines `LawfulOrderInf.ofLE` and `LawfulOrderMin.ofLE`.
-/
public theorem LawfulOrderLT.ofLE {α : Type u} [OrderData α] [LT α] [LE α] [LawfulOrderLE α]
    (lt_iff : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) : LawfulOrderLT α where
  lt_iff := by simpa [LawfulOrderLE.le_iff] using lt_iff

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma characterizes
in terms of `LE α` when a `Min α` instance "behaves like an infimum operator".
-/
public theorem LawfulOrderInf.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (le_min_iff : ∀ a b c : α, a ≤ Min.min b c ↔ a ≤ b ∧ a ≤ c) : LawfulOrderInf α where
  le_min_iff := by simpa [LawfulOrderLE.le_iff] using le_min_iff

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
  toMinEqOr := ⟨min_eq_or⟩

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma characterizes
in terms of `LE α` when a `Max α` instance "behaves like an supremum operator".
-/
public def LawfulOrderSup.ofLE {α : Type u} [OrderData α] [Max α] [LE α] [LawfulOrderLE α]
    (max_le_iff : ∀ a b c : α, Max.max a b ≤ c ↔ a ≤ c ∧ b ≤ c) : LawfulOrderSup α where
  max_le_iff := by simpa [LawfulOrderLE.le_iff] using max_le_iff

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
  toMaxEqOr := ⟨max_eq_or⟩

end OfLE

section OfLT

/--
Creates an `OrderData α` instance from an `LT α` instance.

This only makes sense for asymmetric `LT α` instances (see `Std.Asymm`).
-/
public def OrderData.ofLT (α : Type u) [LT α] : OrderData α where
  IsLE a b := ¬ b < a

/--
The `OrderData α` instance obtained from an asymmetric `LT α` instance is compatible with said
`LT α` instance.
-/
public instance LawfulOrderLT.ofLT {α : Type u} [LT α] [i : Asymm (α := α) (· < ·)] :
    haveI := OrderData.ofLT α
    LawfulOrderLT α :=
  letI := OrderData.ofLT α
  { lt_iff a b := by simpa [OrderData.ofLT, Classical.not_not] using i.asymm a b }

/--
If an `OrderData α` instance is compatible with an asymmetric `LT α` instance the negation of which
is transitive, then the `OrderData α` instance is a linear order.
-/
public theorem IsLinearPreorder.ofLT {α : Type u} [LT α]
    (lt_asymm : ∀ a b : α, a < b → ¬ b < a)
    (not_lt_trans : ∀ a b c : α, ¬ a < b → ¬ b < c → ¬ a < c) :
    haveI : OrderData α := .ofLT α
    IsLinearPreorder α :=
  letI : OrderData α := .ofLT α
  { le_trans := by simpa [OrderData.ofLT] using fun a b c hab hbc => not_lt_trans c b a hbc hab
    le_total a b := by
      apply Or.symm
      open Classical in simpa [OrderData.ofLT, Decidable.imp_iff_not_or] using lt_asymm a b
    le_refl a := by
      open Classical in simpa [OrderData.ofLT] using lt_asymm a a }

/--
If an `OrderData α` instance is compatible with an asymmetric `LT α` instance the negation of which
is transitive and antisymmetric, then the `OrderData α` instance is a linear order.
-/
public theorem IsLinearOrder.ofLT {α : Type u} [LT α]
    (lt_asymm : ∀ a b : α, a < b → ¬ b < a)
    (not_lt_trans : ∀ a b c : α, ¬ a < b → ¬ b < c → ¬ a < c)
    (not_lt_antisymm : ∀ a b : α, ¬ a < b → ¬ b < a → a = b) :
    haveI : OrderData α := .ofLT α
    IsLinearOrder α :=
  letI : OrderData α := .ofLT α
  haveI : IsLinearPreorder α := .ofLT lt_asymm not_lt_trans
  { le_antisymm := by simpa [OrderData.ofLT] using fun a b hab hba => not_lt_antisymm a b hba hab }

/--
Returns a `LawfulOrderLT α` instance given certain properties.

If an `OrderData α` instance is compatible with an `LT α` instance, then this lemma derives
a `LawfulOrderMin α` instance from two properties involving `LE α` and `Min α` instances.

This convenience lemma combines `LawfulOrderInf.ofLE` and `LawfulOrderMin.ofLE`.
-/
public theorem LawfulOrderLE.ofLT {α : Type u} [LT α] [LE α]
    (le_iff : ∀ a b : α, a ≤ b ↔ ¬ b < a) :
    haveI : OrderData α := .ofLT α
    LawfulOrderLE α :=
  letI : OrderData α := .ofLT α
  { le_iff := by simp [le_iff, OrderData.ofLT] }

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma characterizes
in terms of `LE α` when a `Min α` instance "behaves like an infimum operator".
-/
public theorem LawfulOrderInf.ofLT {α : Type u} [Min α] [LT α]
    (min_lt_iff : ∀ a b c : α, Min.min b c < a ↔ b < a ∨ c < a) :
    haveI : OrderData α := .ofLT α
    LawfulOrderInf α :=
  letI : OrderData α := .ofLT α
  { le_min_iff a b c := by
      open Classical in
      simp only [OrderData.ofLT, ← Decidable.not_iff_not (a := ¬ min b c < a)]
      simpa [Decidable.imp_iff_not_or] using min_lt_iff a b c }

/--
Returns a `LawfulOrderMin α` instance given certain properties.

If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma derives
a `LawfulOrderMin α` instance from two properties involving `LE α` and `Min α` instances.

This convenience lemma combines `LawfulOrderInf.ofLE` and `LawfulOrderMin.ofLE`.
-/
public theorem LawfulOrderMin.ofLT {α : Type u} [Min α] [LT α]
    (min_lt_iff : ∀ a b c : α, Min.min b c < a ↔ b < a ∨ c < a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) :
    haveI : OrderData α := .ofLT α
    LawfulOrderMin α :=
  letI : OrderData α := .ofLT α
  { toLawfulOrderInf := .ofLT min_lt_iff
    toMinEqOr := ⟨min_eq_or⟩ }

/--
If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma characterizes
in terms of `LE α` when a `Max α` instance "behaves like an supremum operator".
-/
public def LawfulOrderSup.ofLT {α : Type u} [Max α] [LT α]
    (lt_max_iff : ∀ a b c : α, c < Max.max a b ↔ c < a ∨ c < b) :
    haveI : OrderData α := .ofLT α
    LawfulOrderSup α :=
  letI : OrderData α := .ofLT α
  { max_le_iff a b c := by
      open Classical in
      simp only [OrderData.ofLT, ← Decidable.not_iff_not ( a := ¬ c < max a b)]
      simpa [Decidable.imp_iff_not_or] using lt_max_iff a b c }

/--
Returns a `LawfulOrderMax α` instance given certain properties.

If an `OrderData α` instance is compatible with an `LE α` instance, then this lemma derives
a `LawfulOrderMax α` instance from two properties involving `LE α` and `Max α` instances.

This convenience lemma combines `LawfulOrderSup.ofLE` and `LawfulOrderMax.ofLE`.
-/
public def LawfulOrderMax.ofLT {α : Type u} [Max α] [LT α]
    (lt_max_iff : ∀ a b c : α, c < Max.max a b ↔ c < a ∨ c < b)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) :
    haveI : OrderData α := .ofLT α
    LawfulOrderMax α :=
  letI : OrderData α := .ofLT α
  { toLawfulOrderSup := .ofLT lt_max_iff
    toMaxEqOr := ⟨max_eq_or⟩ }

end OfLT

end Std
