/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Init.Data.Ord

/-!
# Type classes related to `Ord`

This file provides several typeclasses encode properties of an `Ord` instance. For each typeclass,
there is also a variant that does not depend on an `Ord` instance and takes an explicit comparison
function `cmp : α → α → Ordering` instead.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u

namespace Std

section Refl

/-- A typeclass for comparison functions `cmp` for which `cmp a a = .eq` for all `a`. -/
class ReflCmp {α : Type u} (cmp : α → α → Ordering) : Prop where
  /-- Comparison is reflexive. -/
  compare_self {a : α} : cmp a a = .eq

export ReflCmp (compare_self)

/-- A typeclasses for ordered types for which `compare a a = .eq` for all `a`. -/
abbrev ReflOrd (α : Type u) [Ord α] := ReflCmp (compare : α → α → Ordering)

attribute [simp] compare_self

end Refl

section Oriented

/--
A typeclass for functions `α → α → Ordering` which are oriented: flipping the arguments amounts
to applying `Ordering.swap` to the return value.
-/
class OrientedCmp {α : Type u} (cmp : α → α → Ordering) : Prop where
  /-- Swapping the arguments to `cmp` swaps the outcome. -/
  eq_swap {a b : α} : cmp a b = (cmp b a).swap

/--
A typeclass for types with an oriented comparison function: flipping the arguments amounts to
applying `Ordering.swap` to the return value.
-/
abbrev OrientedOrd (α : Type u) [Ord α] := OrientedCmp (compare : α → α → Ordering)

variable {α : Type u} {cmp : α → α → Ordering}

instance [OrientedCmp cmp] : ReflCmp cmp where
  compare_self := Ordering.eq_eq_of_eq_swap OrientedCmp.eq_swap

theorem OrientedCmp.gt_iff_lt [OrientedCmp cmp] {a b : α} : cmp a b = .gt ↔ cmp b a = .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.lt_of_gt [OrientedCmp cmp] {a b : α} : cmp a b = .gt → cmp b a = .lt :=
  OrientedCmp.gt_iff_lt.1

theorem OrientedCmp.gt_of_lt [OrientedCmp cmp] {a b : α} : cmp a b = .lt → cmp b a = .gt :=
  OrientedCmp.gt_iff_lt.2

theorem OrientedCmp.eq_comm [OrientedCmp cmp] {a b : α} : cmp a b = .eq ↔ cmp b a = .eq := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp [Ordering.swap]

theorem OrientedCmp.eq_symm [OrientedCmp cmp] {a b : α} : cmp a b = .eq → cmp b a = .eq :=
  OrientedCmp.eq_comm.1

theorem OrientedCmp.not_isLE_of_lt [OrientedCmp cmp] {a b : α} :
    cmp a b = .lt → ¬(cmp b a).isLE := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  simp

theorem OrientedCmp.not_lt_of_isLE [OrientedCmp cmp] {a b : α} :
    (cmp a b).isLE → cmp b a ≠ .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.not_lt_of_lt [OrientedCmp cmp] {a b : α} :
    cmp a b = .lt → cmp b a ≠ .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.lt_of_not_isLE [OrientedCmp cmp] {a b : α} :
    ¬(cmp a b).isLE → cmp b a = .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

end Oriented

section Trans

/-- A typeclass for functions `α → α → Ordering` which are transitive. -/
class TransCmp {α : Type u} (cmp : α → α → Ordering) extends OrientedCmp cmp : Prop where
  /-- Transitivity of `cmp`, expressed via `Ordering.isLE`. -/
  le_trans {a b c : α} : (cmp a b).isLE → (cmp b c).isLE → (cmp a c).isLE

/-- A typeclass for types with a transitive ordering function. -/
abbrev TransOrd (α : Type u) [Ord α] := TransCmp (compare : α → α → Ordering)

variable {α : Type u} {cmp : α → α → Ordering}

theorem TransCmp.lt_of_lt_of_eq [TransCmp cmp] {a b c : α} (hab : cmp a b = .lt)
    (hbc : cmp b c = .eq) : cmp a c = .lt := by
  apply OrientedCmp.lt_of_not_isLE
  intro hca
  suffices cmp a b ≠ .lt from absurd hab this
  exact OrientedCmp.not_lt_of_isLE (TransCmp.le_trans (Ordering.isLE_of_eq_eq hbc) hca)

theorem TransCmp.lt_of_eq_of_lt [TransCmp cmp] {a b c : α} (hab : cmp a b = .eq)
    (hbc : cmp b c = .lt) : cmp a c = .lt := by
  apply OrientedCmp.lt_of_not_isLE
  intro hca
  suffices cmp b c ≠ .lt from absurd hbc this
  exact OrientedCmp.not_lt_of_isLE (TransCmp.le_trans hca (Ordering.isLE_of_eq_eq hab))

theorem TransCmp.lt_trans [TransCmp cmp] {a b c : α} (hab : cmp a b = .lt) (hbc : cmp b c = .lt) :
    cmp a c = .lt := by
  cases hac : cmp a c
  · rfl
  · suffices cmp a b ≠ .lt from absurd hab this
    exact OrientedCmp.not_lt_of_isLE (TransCmp.le_trans (Ordering.isLE_of_eq_lt hbc)
      (Ordering.isLE_of_eq_eq (OrientedCmp.eq_symm hac)))
  · suffices cmp a b ≠ .lt from absurd hab this
    exact OrientedCmp.not_lt_of_isLE (TransCmp.le_trans (Ordering.isLE_of_eq_lt hbc)
      (Ordering.isLE_of_eq_lt (OrientedCmp.lt_of_gt hac)))

theorem TransCmp.lt_of_lt_of_isLE [TransCmp cmp] {a b c : α} (hab : cmp a b = .lt)
    (hbc : (cmp b c).isLE) : cmp a c = .lt := by
  rw [Ordering.isLE_iff_eq_lt_or_eq_eq] at hbc
  obtain hbc|hbc := hbc
  · exact TransCmp.lt_trans hab hbc
  · exact TransCmp.lt_of_lt_of_eq hab hbc

theorem TransCmp.lt_of_isLE_of_lt [TransCmp cmp] {a b c : α} (hab : (cmp a b).isLE)
    (hbc : cmp b c = .lt) : cmp a c = .lt := by
  rw [Ordering.isLE_iff_eq_lt_or_eq_eq] at hab
  obtain hab|hab := hab
  · exact TransCmp.lt_trans hab hbc
  · exact TransCmp.lt_of_eq_of_lt hab hbc

theorem TransCmp.isLE_antisymm [TransCmp cmp] {a b : α} (h₁ : cmp a b |>.isLE) (h₂ : cmp b a |>.isLE) :
    cmp a b = .eq := by
  rw [OrientedCmp.eq_swap (cmp := cmp)] at h₂
  cases h : cmp a b <;> rw [h] at h₁ h₂ <;> simp at h₁ h₂

theorem TransCmp.isGE_antisymm [TransCmp cmp] {a b : α} (h₁ : cmp a b |>.isGE) (h₂ : cmp b a |>.isGE) :
    cmp a b = .eq := by
  rw [OrientedCmp.eq_swap (cmp := cmp)] at h₂
  cases h : cmp a b <;> rw [h] at h₁ h₂ <;> simp at h₁ h₂

theorem TransCmp.eq_trans [TransCmp cmp] {a b c : α} (hab : cmp a b = .eq)
    (hbc : cmp b c = .eq) : cmp a c = .eq := by
  apply Ordering.eq_eq_of_isLE_of_isLE_swap
  · exact TransCmp.le_trans (Ordering.isLE_of_eq_eq hab) (Ordering.isLE_of_eq_eq hbc)
  · rw [← OrientedCmp.eq_swap]
    exact TransCmp.le_trans (Ordering.isLE_of_eq_eq (OrientedCmp.eq_symm hbc))
      (Ordering.isLE_of_eq_eq (OrientedCmp.eq_symm hab))

theorem TransCmp.congr_left [TransCmp cmp] {a b c : α} (hab : cmp a b = .eq) :
    cmp a c = cmp b c := by
  cases hbc : cmp b c with
  | lt => exact TransCmp.lt_of_eq_of_lt hab hbc
  | eq => exact TransCmp.eq_trans hab hbc
  | gt =>
      exact OrientedCmp.gt_of_lt
        (TransCmp.lt_of_lt_of_eq (OrientedCmp.lt_of_gt hbc) (OrientedCmp.eq_symm hab))

theorem TransCmp.congr_right [TransCmp cmp] {a b c : α} (hbc : cmp b c = .eq) :
    cmp a b = cmp a c := by
  cases hab : cmp a b with
  | lt => exact TransCmp.lt_of_lt_of_eq hab hbc |>.symm
  | eq => exact TransCmp.eq_trans hab hbc |>.symm
  | gt =>
    exact OrientedCmp.gt_of_lt
      (TransCmp.lt_of_eq_of_lt (OrientedCmp.eq_symm hbc) (OrientedCmp.lt_of_gt hab)) |>.symm

end Trans

section LawfulEq

/--
A typeclass for comparison functions satisfying `cmp a b = .eq` if and only if the logical equality
`a = b` holds.
-/
class LawfulEqCmp {α : Type u} (cmp : α → α → Ordering) extends ReflCmp cmp : Prop where
  /-- If two values compare equal, then they are logically equal. -/
  eq_of_compare {a b : α} : cmp a b = .eq → a = b

/--
A typeclass for types with a comparison function that satisfies `compare a b = .eq` if and only if
the logical equality `a = b` holds.
-/
abbrev LawfulEqOrd (α : Type u) [Ord α] := LawfulEqCmp (compare : α → α → Ordering)

variable {α : Type u} {cmp : α → α → Ordering} [LawfulEqCmp cmp]

@[simp]
theorem compare_eq_iff_eq {a b : α} : cmp a b = .eq ↔ a = b :=
  ⟨LawfulEqCmp.eq_of_compare, by rintro rfl; simp⟩

@[simp]
theorem compare_beq_iff_eq {a b : α} : cmp a b == .eq ↔ a = b :=
  ⟨LawfulEqCmp.eq_of_compare ∘ eq_of_beq, by rintro rfl; simp⟩

end LawfulEq

namespace Internal

variable {α : Type u}

/--
Internal funcion to derive a `BEq` instance from an `Ord` instance in order to connect the
verification machinery for tree maps to the verification machinery for hash maps.
-/
@[local instance]
def beqOfOrd [Ord α] : BEq α where
  beq a b := compare a b == .eq

@[local simp]
theorem beq_eq [Ord α] {a b : α} : (a == b) = (compare a b == .eq) :=
  rfl

theorem equivBEq_of_transOrd [Ord α] [TransOrd α] : EquivBEq α where
  symm {a b} h := by simp_all [OrientedCmp.eq_comm]
  trans h₁ h₂ := by simp_all only [beq_eq, beq_iff_eq]; exact TransCmp.eq_trans h₁ h₂
  refl := by simp

theorem lawfulBEq_of_lawfulEqOrd [Ord α] [LawfulEqOrd α] : LawfulBEq α where
  eq_of_beq hbeq := by simp_all
  rfl := by simp

end Internal

end Std
