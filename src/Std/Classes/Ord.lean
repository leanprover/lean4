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

/-- A typeclasses for ordered types for which `compare a a = .eq` for all `a`. -/
abbrev ReflOrd (α : Type u) [Ord α] := ReflCmp (compare : α → α → Ordering)

@[simp]
theorem ReflOrd.compare_self {α : Type u} [Ord α] [ReflOrd α] {a : α} : compare a a = .eq :=
    ReflCmp.compare_self

export ReflOrd (compare_self)

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

theorem OrientedCmp.isGE_iff_isLE [OrientedCmp cmp] {a b : α} : (cmp a b).isGE ↔ (cmp b a).isLE := by
  rw [OrientedCmp.eq_swap (cmp := cmp)]
  cases cmp b a <;> simp

theorem OrientedCmp.isLE_of_isGE [OrientedCmp cmp] {a b : α} : (cmp b a).isGE → (cmp a b).isLE :=
  OrientedCmp.isGE_iff_isLE.1

theorem OrientedCmp.isGE_of_isLE [OrientedCmp cmp] {a b : α} : (cmp b a).isLE → (cmp a b).isGE :=
  OrientedCmp.isGE_iff_isLE.2

theorem OrientedCmp.eq_comm [OrientedCmp cmp] {a b : α} : cmp a b = .eq ↔ cmp b a = .eq := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp [Ordering.swap]

theorem OrientedCmp.eq_symm [OrientedCmp cmp] {a b : α} : cmp a b = .eq → cmp b a = .eq :=
  OrientedCmp.eq_comm.1

theorem OrientedCmp.not_isLE_of_lt [OrientedCmp cmp] {a b : α} :
    cmp a b = .lt → ¬(cmp b a).isLE := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  simp

theorem OrientedCmp.not_isGE_of_gt [OrientedCmp cmp] {a b : α} :
    cmp a b = .gt → ¬(cmp b a).isGE := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  simp

theorem OrientedCmp.not_lt_of_isLE [OrientedCmp cmp] {a b : α} :
    (cmp a b).isLE → cmp b a ≠ .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.not_gt_of_isGE [OrientedCmp cmp] {a b : α} :
    (cmp a b).isGE → cmp b a ≠ .gt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.not_lt_of_lt [OrientedCmp cmp] {a b : α} :
    cmp a b = .lt → cmp b a ≠ .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.not_gt_of_gt [OrientedCmp cmp] {a b : α} :
    cmp a b = .gt → cmp b a ≠ .gt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.lt_of_not_isLE [OrientedCmp cmp] {a b : α} :
    ¬(cmp a b).isLE → cmp b a = .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.gt_of_not_isGE [OrientedCmp cmp] {a b : α} :
    ¬(cmp a b).isGE → cmp b a = .gt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

end Oriented

section Trans

/-- A typeclass for functions `α → α → Ordering` which are transitive. -/
class TransCmp {α : Type u} (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- Transitivity of `cmp`, expressed via `Ordering.isLE`. -/
  isLE_trans {a b c : α} : (cmp a b).isLE → (cmp b c).isLE → (cmp a c).isLE

/-- A typeclass for types with a transitive ordering function. -/
abbrev TransOrd (α : Type u) [Ord α] := TransCmp (compare : α → α → Ordering)

variable {α : Type u} {cmp : α → α → Ordering}

theorem TransCmp.isGE_trans [TransCmp cmp] {a b c : α} (h₁ : (cmp a b).isGE) (h₂ : (cmp b c).isGE) :
    (cmp a c).isGE := by
  rw [OrientedCmp.isGE_iff_isLE] at *
  exact TransCmp.isLE_trans h₂ h₁

theorem TransCmp.lt_of_lt_of_eq [TransCmp cmp] {a b c : α} (hab : cmp a b = .lt)
    (hbc : cmp b c = .eq) : cmp a c = .lt := by
  apply OrientedCmp.lt_of_not_isLE
  intro hca
  suffices cmp a b ≠ .lt from absurd hab this
  exact OrientedCmp.not_lt_of_isLE (TransCmp.isLE_trans (Ordering.isLE_of_eq_eq hbc) hca)

theorem TransCmp.lt_of_eq_of_lt [TransCmp cmp] {a b c : α} (hab : cmp a b = .eq)
    (hbc : cmp b c = .lt) : cmp a c = .lt := by
  apply OrientedCmp.lt_of_not_isLE
  intro hca
  suffices cmp b c ≠ .lt from absurd hbc this
  exact OrientedCmp.not_lt_of_isLE (TransCmp.isLE_trans hca (Ordering.isLE_of_eq_eq hab))

theorem TransCmp.gt_of_eq_of_gt [TransCmp cmp] {a b c : α} (hab : cmp a b = .eq)
    (hbc : cmp b c = .gt) : cmp a c = .gt := by
  rw [OrientedCmp.gt_iff_lt] at *
  exact TransCmp.lt_of_lt_of_eq hbc (OrientedCmp.eq_symm hab)

theorem TransCmp.gt_of_gt_of_eq [TransCmp cmp] {a b c : α} (hab : cmp a b = .gt)
    (hbc : cmp b c = .eq) : cmp a c = .gt := by
  rw [OrientedCmp.gt_iff_lt] at *
  exact TransCmp.lt_of_eq_of_lt (OrientedCmp.eq_symm hbc) hab

theorem TransCmp.lt_trans [TransCmp cmp] {a b c : α} (hab : cmp a b = .lt) (hbc : cmp b c = .lt) :
    cmp a c = .lt := by
  cases hac : cmp a c
  · rfl
  · suffices cmp a b ≠ .lt from absurd hab this
    exact OrientedCmp.not_lt_of_isLE (TransCmp.isLE_trans (Ordering.isLE_of_eq_lt hbc)
      (Ordering.isLE_of_eq_eq (OrientedCmp.eq_symm hac)))
  · suffices cmp a b ≠ .lt from absurd hab this
    exact OrientedCmp.not_lt_of_isLE (TransCmp.isLE_trans (Ordering.isLE_of_eq_lt hbc)
      (Ordering.isLE_of_eq_lt (OrientedCmp.lt_of_gt hac)))

theorem TransCmp.gt_trans [TransCmp cmp] {a b c : α} (hab : cmp a b = .gt) (hbc : cmp b c = .gt) :
    cmp a c = .gt := by
  rw [OrientedCmp.gt_iff_lt (cmp := cmp)] at *
  exact lt_trans hbc hab

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

theorem TransCmp.gt_of_gt_of_isGE [TransCmp cmp] {a b c : α} (hab : cmp a b = .gt)
    (hbc : (cmp b c).isGE) : cmp a c = .gt := by
  rw [OrientedCmp.gt_iff_lt, OrientedCmp.isGE_iff_isLE] at *
  exact TransCmp.lt_of_isLE_of_lt hbc hab

theorem TransCmp.gt_of_isGE_of_gt [TransCmp cmp] {a b c : α} (hab : (cmp a b).isGE)
    (hbc : cmp b c = .gt) : cmp a c = .gt := by
  rw [OrientedCmp.gt_iff_lt, OrientedCmp.isGE_iff_isLE] at *
  exact TransCmp.lt_of_lt_of_isLE hbc hab

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
  · exact TransCmp.isLE_trans (Ordering.isLE_of_eq_eq hab) (Ordering.isLE_of_eq_eq hbc)
  · rw [← OrientedCmp.eq_swap]
    exact TransCmp.isLE_trans (Ordering.isLE_of_eq_eq (OrientedCmp.eq_symm hbc))
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

This typeclass distinguishes itself from `LawfulBEqCmp` by using logical equality (`=`) instead of
boolean equality (`==`).
-/
class LawfulEqCmp {α : Type u} (cmp : α → α → Ordering) : Prop extends ReflCmp cmp where
  /-- If two values compare equal, then they are logically equal. -/
  eq_of_compare {a b : α} : cmp a b = .eq → a = b

/--
A typeclass for types with a comparison function that satisfies `compare a b = .eq` if and only if
the logical equality `a = b` holds.

This typeclass distinguishes itself from `LawfulBEqOrd` by using logical equality (`=`) instead of
boolean equality (`==`).
-/
abbrev LawfulEqOrd (α : Type u) [Ord α] := LawfulEqCmp (compare : α → α → Ordering)

variable {α : Type u} {cmp : α → α → Ordering} [LawfulEqCmp cmp]

@[simp]
theorem compare_eq_iff_eq {a b : α} : cmp a b = .eq ↔ a = b :=
  ⟨LawfulEqCmp.eq_of_compare, by rintro rfl; exact ReflCmp.compare_self⟩

@[simp]
theorem compare_beq_iff_eq {a b : α} : cmp a b == .eq ↔ a = b :=
  ⟨LawfulEqCmp.eq_of_compare ∘ eq_of_beq, by rintro rfl; simp⟩

end LawfulEq

section LawfulBEq

/--
A typeclass for comparison functions satisfying `cmp a b = .eq` if and only if the boolean equality
`a == b` holds.

This typeclass distinguishes itself from `LawfulEqCmp` by using boolean equality (`==`) instead of
logical equality (`=`).
-/
class LawfulBEqCmp {α : Type u} [BEq α] (cmp : α → α → Ordering) : Prop where
  /-- If two values compare equal, then they are logically equal. -/
  compare_eq_iff_beq {a b : α} : cmp a b = .eq ↔ a == b

theorem LawfulBEqCmp.not_compare_eq_iff_beq_eq_false {α : Type u} [BEq α] {cmp}
    [LawfulBEqCmp (α := α) cmp] {a b : α} : ¬ cmp a b = .eq ↔ (a == b) = false := by
  rw [Bool.eq_false_iff, ne_eq, not_congr]
  exact compare_eq_iff_beq

/--
A typeclass for types with a comparison function that satisfies `compare a b = .eq` if and only if
the boolean equality `a == b` holds.

This typeclass distinguishes itself from `LawfulEqOrd` by using boolean equality (`==`) instead of
logical equality (`=`).
-/
abbrev LawfulBEqOrd (α : Type u) [BEq α] [Ord α] := LawfulBEqCmp (compare : α → α → Ordering)

variable {α : Type u} [BEq α] {cmp : α → α → Ordering}

theorem LawfulBEqOrd.compare_eq_iff_beq {α : Type u} {_ : Ord α} {_ : BEq α}
    [LawfulBEqOrd α] {a b : α} : compare a b = .eq ↔ (a == b) = true :=
  LawfulBEqCmp.compare_eq_iff_beq

theorem LawfulBEqOrd.not_compare_eq_iff_beq_eq_false {α : Type u} {_ : BEq α} {_ : Ord α}
    [LawfulBEqOrd α] {a b : α} : ¬ compare a b = .eq ↔ (a == b) = false :=
  LawfulBEqCmp.not_compare_eq_iff_beq_eq_false

export LawfulBEqOrd (compare_eq_iff_beq not_compare_eq_iff_beq_eq_false)

instance [LawfulEqCmp cmp] [LawfulBEq α] :
    LawfulBEqCmp cmp where
  compare_eq_iff_beq := compare_eq_iff_eq.trans beq_iff_eq.symm

theorem LawfulBEqCmp.equivBEq [inst : LawfulBEqCmp cmp] [TransCmp cmp] : EquivBEq α where
  refl := inst.compare_eq_iff_beq.mp ReflCmp.compare_self
  symm := by
    simp only [← inst.compare_eq_iff_beq]
    exact OrientedCmp.eq_symm
  trans := by
    simp only [← inst.compare_eq_iff_beq]
    exact TransCmp.eq_trans

instance LawfulBEqOrd.equivBEq [Ord α] [LawfulBEqOrd α] [TransOrd α] : EquivBEq α :=
  LawfulBEqCmp.equivBEq (cmp := compare)

theorem LawfulBEqCmp.lawfulBEq [inst : LawfulBEqCmp cmp] [LawfulEqCmp cmp] : LawfulBEq α where
  rfl := by simp [← inst.compare_eq_iff_beq, compare_eq_iff_eq]
  eq_of_beq := by simp [← inst.compare_eq_iff_beq, compare_eq_iff_eq]

instance LawfulBEqOrd.lawfulBEq [Ord α] [LawfulBEqOrd α] [LawfulEqOrd α] : LawfulBEq α :=
  LawfulBEqCmp.lawfulBEq (cmp := compare)

instance LawfulBEqCmp.lawfulBEqCmp [inst : LawfulBEqCmp cmp] [LawfulBEq α] : LawfulEqCmp cmp where
  compare_self := by simp only [compare_eq_iff_beq, beq_self_eq_true, implies_true]
  eq_of_compare := by simp only [compare_eq_iff_beq, beq_iff_eq, imp_self, implies_true]

theorem LawfulBEqOrd.lawfulBEqOrd [Ord α] [LawfulBEqOrd α] [LawfulBEq α] : LawfulEqOrd α :=
  LawfulBEqCmp.lawfulBEqCmp

end LawfulBEq

namespace Internal

variable {α : Type u}

/--
Internal funcion to derive a `BEq` instance from an `Ord` instance in order to connect the
verification machinery for tree maps to the verification machinery for hash maps.
-/
@[local instance]
def beqOfOrd [Ord α] : BEq α where
  beq a b := compare a b == .eq

instance {_ : Ord α} : LawfulBEqOrd α where
  compare_eq_iff_beq {a b} := by simp only [beqOfOrd, beq_iff_eq]

@[local simp]
theorem beq_eq [Ord α] {a b : α} : (a == b) = (compare a b == .eq) :=
  rfl

theorem beq_iff [Ord α] {a b : α} : (a == b) = true ↔ compare a b = .eq := by
  rw [beq_eq, beq_iff_eq]

theorem eq_beqOfOrd_of_lawfulBEqOrd [Ord α] (inst : BEq α) [instLawful : LawfulBEqOrd α] :
    inst = beqOfOrd := by
  cases inst; rename_i instBEq
  congr; ext a b
  rw [Bool.eq_iff_iff, beq_iff_eq, instLawful.compare_eq_iff_beq]
  rfl

theorem equivBEq_of_transOrd [Ord α] [TransOrd α] : EquivBEq α where
  symm {a b} h := by simp_all [OrientedCmp.eq_comm]
  trans h₁ h₂ := by simp_all only [beq_eq, beq_iff_eq]; exact TransCmp.eq_trans h₁ h₂
  refl := by simp only [beq_eq, beq_iff_eq]; exact compare_self

theorem lawfulBEq_of_lawfulEqOrd [Ord α] [LawfulEqOrd α] : LawfulBEq α where
  eq_of_beq hbeq := by simp_all
  rfl := by simp

end Internal

end Std
