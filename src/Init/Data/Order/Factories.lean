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
This instance is only publicly defined in `Init.Data.Order.Lemmas`.
-/
instance {r : α → α → Prop} [Total r] : Refl r where
  refl a := by simpa using Total.total a a

/--
If an `LE α` instance is reflexive and transitive, then it represents a preorder.
-/
public theorem IsPreorder.of_le {α : Type u} [LE α]
    (le_refl : Std.Refl (α := α) (· ≤ ·) := by exact inferInstance)
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance) :
    IsPreorder α where
  le_refl := le_refl.refl
  le_trans _ _ _ := le_trans.trans

/--
If an `LE α` instance is transitive and total, then it represents a linear preorder.
-/
public theorem IsLinearPreorder.of_le {α : Type u} [LE α]
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance)
    (le_total : Total (α := α) (· ≤ ·) := by exact inferInstance) :
    IsLinearPreorder α where
  toIsPreorder := .of_le
  le_total := le_total.total

/--
If an `LE α` is reflexive, antisymmetric and transitive, then it represents a partial order.
-/
public theorem IsPartialOrder.of_le {α : Type u} [LE α]
    (le_refl : Std.Refl (α := α) (· ≤ ·) := by exact inferInstance)
    (le_antisymm : Std.Antisymm (α := α) (· ≤ ·) := by exact inferInstance)
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance) :
    IsPartialOrder α where
  toIsPreorder := .of_le
  le_antisymm := le_antisymm.antisymm

/--
If an `LE α` instance is antisymmetric, transitive and total, then it represents a linear order.
-/
public theorem IsLinearOrder.of_le {α : Type u} [LE α]
    (le_antisymm : Std.Antisymm (α := α) (· ≤ ·) := by exact inferInstance)
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance)
    (le_total : Total (α := α) (· ≤ ·) := by exact inferInstance) :
    IsLinearOrder α where
  toIsLinearPreorder := .of_le
  le_antisymm := le_antisymm.antisymm

/--
This lemma derives a `LawfulOrderLT α` instance from a property involving an `LE α` instance.
-/
public theorem LawfulOrderLT.of_le {α : Type u} [LT α] [LE α]
    (lt_iff : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) : LawfulOrderLT α where
  lt_iff := lt_iff

/--
This lemma derives a `LawfulOrderBEq α` instance from a property involving an `LE α` instance.
-/
public theorem LawfulOrderBEq.of_le {α : Type u} [BEq α] [LE α]
    (beq_iff : ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a) : LawfulOrderBEq α where
  beq_iff_le_and_ge := by simp [beq_iff]

/--
This lemma characterizes in terms of `LE α` when a `Min α` instance "behaves like an infimum
operator".
-/
public theorem LawfulOrderInf.of_le {α : Type u} [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) : LawfulOrderInf α where
  le_min_iff := le_min_iff

/--
Returns a `LawfulOrderMin α` instance given certain properties.

This lemma derives a `LawfulOrderMin α` instance from two properties involving `LE α` and `Min α`
instances.

The produced instance entails `LawfulOrderInf α` and `MinEqOr α`.
-/
public theorem LawfulOrderMin.of_le {α : Type u} [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) : LawfulOrderMin α where
  toLawfulOrderInf := .of_le le_min_iff
  toMinEqOr := ⟨min_eq_or⟩

/--
This lemma characterizes in terms of `LE α` when a `Max α` instance "behaves like a supremum
operator".
-/
public def LawfulOrderSup.of_le {α : Type u} [Max α] [LE α]
    (max_le_iff : ∀ a b c : α, max a b ≤ c ↔ a ≤ c ∧ b ≤ c) : LawfulOrderSup α where
  max_le_iff := max_le_iff

/--
Returns a `LawfulOrderMax α` instance given certain properties.

This lemma derives a `LawfulOrderMax α` instance from two properties involving `LE α` and `Max α`
instances.

The produced instance entails `LawfulOrderSup α` and `MaxEqOr α`.
-/
public def LawfulOrderMax.of_le {α : Type u} [Max α] [LE α]
    (max_le_iff : ∀ a b c : α, max a b ≤ c ↔ a ≤ c ∧ b ≤ c)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) : LawfulOrderMax α where
  toLawfulOrderSup := .of_le max_le_iff
  toMaxEqOr := ⟨max_eq_or⟩

end OfLE

section OfLT

/--
Creates a *total* `LE α` instance from an `LT α` instance.

This only makes sense for asymmetric `LT α` instances (see `Std.Asymm`).
-/
public def LE.ofLT (α : Type u) [LT α] : LE α where
  le a b := ¬ b < a

/--
The `LE α` instance obtained from an asymmetric `LT α` instance is compatible with said
`LT α` instance.
-/
public instance LawfulOrderLT.of_lt {α : Type u} [LT α] [i : Asymm (α := α) (· < ·)] :
    haveI := LE.ofLT α
    LawfulOrderLT α :=
  letI := LE.ofLT α
  { lt_iff a b := by simpa [LE.ofLT, Classical.not_not] using i.asymm a b }

/--
If an `LT α` instance is asymmetric and its negation is transitive, then `LE.ofLT α` represents a
linear preorder.
-/
public theorem IsLinearPreorder.of_lt {α : Type u} [LT α]
    (lt_asymm : Asymm (α := α) (· < ·) := by exact inferInstance)
    (not_lt_trans : Trans (α := α) (¬ · < ·) (¬ · < ·) (¬ · < ·) := by exact inferInstance) :
    haveI := LE.ofLT α
    IsLinearPreorder α :=
  letI := LE.ofLT α
  { le_trans := by simpa [LE.ofLT] using fun a b c hab hbc => not_lt_trans.trans hbc hab
    le_total a b := by
      apply Or.symm
      open Classical in simpa [LE.ofLT, Decidable.imp_iff_not_or] using lt_asymm.asymm a b
    le_refl a := by
      open Classical in simpa [LE.ofLT] using lt_asymm.asymm a a }

/--
If an `LT α` instance is asymmetric and its negation is transitive and antisymmetric, then
`LE.ofLT α` represents a linear order.
-/
public theorem IsLinearOrder.of_lt {α : Type u} [LT α]
    (lt_asymm : Asymm (α := α) (· < ·) := by exact inferInstance)
    (not_lt_trans : Trans (α := α) (¬ · < ·) (¬ · < ·) (¬ · < ·) := by exact inferInstance)
    (not_lt_antisymm : Antisymm (α := α) (¬ · < ·) := by exact inferInstance) :
    haveI := LE.ofLT α
    IsLinearOrder α :=
  letI := LE.ofLT α
  haveI : IsLinearPreorder α := .of_lt
  { le_antisymm := by
      simpa [LE.ofLT] using fun a b hab hba => not_lt_antisymm.antisymm a b hba hab }

/--
This lemma characterizes in terms of `LT α` when a `Min α` instance
"behaves like an infimum operator" with respect to `LE.ofLT α`.
-/
public theorem LawfulOrderInf.of_lt {α : Type u} [Min α] [LT α]
    (min_lt_iff : ∀ a b c : α, min b c < a ↔ b < a ∨ c < a) :
    haveI := LE.ofLT α
    LawfulOrderInf α :=
  letI := LE.ofLT α
  { le_min_iff a b c := by
      open Classical in
      simp only [LE.ofLT, ← Decidable.not_iff_not (a := ¬ min b c < a)]
      simpa [Decidable.imp_iff_not_or] using min_lt_iff a b c }

/--
Derives a `LawfulOrderMin α` instance for `LE.ofLT` from two properties involving
`LT α` and `Min α` instances.

The produced instance entails `LawfulOrderInf α` and `MinEqOr α`.
-/
public theorem LawfulOrderMin.of_lt {α : Type u} [Min α] [LT α]
    (min_lt_iff : ∀ a b c : α, min b c < a ↔ b < a ∨ c < a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) :
    haveI := LE.ofLT α
    LawfulOrderMin α :=
  letI := LE.ofLT α
  { toLawfulOrderInf := .of_lt min_lt_iff
    toMinEqOr := ⟨min_eq_or⟩ }

/--
This lemma characterizes in terms of `LT α` when a `Max α` instance
"behaves like an supremum operator" with respect to `LE.ofLT α`.
-/
public def LawfulOrderSup.of_lt {α : Type u} [Max α] [LT α]
    (lt_max_iff : ∀ a b c : α, c < max a b ↔ c < a ∨ c < b) :
    haveI := LE.ofLT α
    LawfulOrderSup α :=
  letI := LE.ofLT α
  { max_le_iff a b c := by
      open Classical in
      simp only [LE.ofLT, ← Decidable.not_iff_not ( a := ¬ c < max a b)]
      simpa [Decidable.imp_iff_not_or] using lt_max_iff a b c }

/--
Derives a `LawfulOrderMax α` instance for `LE.ofLT` from two properties involving `LT α` and
`Max α` instances.

The produced instance entails `LawfulOrderSup α` and `MaxEqOr α`.
-/
public def LawfulOrderMax.of_lt {α : Type u} [Max α] [LT α]
    (lt_max_iff : ∀ a b c : α, c < max a b ↔ c < a ∨ c < b)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) :
    haveI := LE.ofLT α
    LawfulOrderMax α :=
  letI := LE.ofLT α
  { toLawfulOrderSup := .of_lt lt_max_iff
    toMaxEqOr := ⟨max_eq_or⟩ }

end OfLT

end Std
