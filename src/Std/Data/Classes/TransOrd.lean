/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u

theorem Ordering.eq_eq_of_isLE_of_isLE_swap {o : Ordering} : o.isLE → o.swap.isLE → o = .eq := by
  cases o <;> simp [isLE, swap]

theorem Ordering.eq_eq_of_eq_swap {o : Ordering} : o = o.swap → o = .eq := by
  cases o <;> simp [swap]

@[simp]
theorem Ordering.isLE_eq_false {o : Ordering} : o.isLE = false ↔ o = gt := by
  cases o <;> simp [isLE]

@[simp]
theorem Ordering.swap_eq_gt {o : Ordering} : o.swap = .gt ↔ o = .lt := by
  cases o <;> simp [swap]

@[simp]
theorem Ordering.swap_eq_lt {o : Ordering} : o.swap = .lt ↔ o = .gt := by
  cases o <;> simp [swap]

theorem Ordering.isLE_iff_eq_lt_or_eq_eq {o : Ordering} : o.isLE ↔ o = .lt ∨ o = .eq := by
  cases o <;> simp [isLE]

theorem Ordering.isLE_of_eq_lt {o : Ordering} : o = .lt → o.isLE := by
  rintro rfl; rfl

theorem Ordering.isLE_of_eq_eq {o : Ordering} : o = .eq → o.isLE := by
  rintro rfl; rfl

theorem Ordering.isGE_of_eq_gt {o : Ordering} : o = .gt → o.isGE := by
  rintro rfl; rfl

theorem Ordering.isGE_of_eq_eq {o : Ordering} : o = .eq → o.isGE := by
  rintro rfl; rfl

-- https://github.com/leanprover/lean4/issues/5295
instance : LawfulBEq Ordering where
  eq_of_beq {a b} := by cases a <;> cases b <;> simp <;> rfl
  rfl {a} := by cases a <;> rfl

theorem LawfulBEq.beq_eq_eq {α : Type u} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · cases h : a == b
    · simpa
    · simpa using eq_of_beq h

/-- Class for functions `α → α → Ordering` which are "oriented". -/
class OrientedCmp {α : Type u} (cmp : α → α → Ordering) : Prop where
  /-- Swapping the arguments to `cmp` swaps the outcome. -/
  eq_swap {a b : α} : cmp a b = (cmp b a).swap

/-- Class for types with an oriented comparison function. -/
class OrientedOrd (α : Type u) [Ord α] extends OrientedCmp (compare : α → α → Ordering) : Prop where

section

variable {α : Type u} {cmp : α → α → Ordering}

theorem OrientedCmp.cmp_self [OrientedCmp cmp] {a : α} : cmp a a = .eq :=
  Ordering.eq_eq_of_eq_swap OrientedCmp.eq_swap

@[simp]
theorem compare_self [Ord α] [OrientedOrd α] {a : α} : compare a a = .eq :=
  OrientedCmp.cmp_self

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

end

/-- Class for functions `α → α → Ordering` which are transitive. -/
class TransCmp {α : Type u} (cmp : α → α → Ordering) extends OrientedCmp cmp : Prop where
  /-- Transitivity of `≤`, expressed via `Ordering.isLE`. -/
  le_trans {a b c : α} : (cmp a b).isLE → (cmp b c).isLE → (cmp a c).isLE

/-- Class for types with a transitive ordering function. -/
class TransOrd (α : Type u) [Ord α] extends OrientedOrd α,
    TransCmp (compare : α → α → Ordering) : Prop where

section

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
  | gt => exact OrientedCmp.gt_of_lt (TransCmp.lt_of_lt_of_eq (OrientedCmp.lt_of_gt hbc) (OrientedCmp.eq_symm hab))

theorem TransCmp.congr_right [TransCmp cmp] {a b c : α} (hbc : cmp b c = .eq) :
    cmp a b = cmp a c := by
  cases hab : cmp a b with
  | lt => exact TransCmp.lt_of_lt_of_eq hab hbc |>.symm
  | eq => exact TransCmp.eq_trans hab hbc |>.symm
  | gt => exact OrientedCmp.gt_of_lt (TransCmp.lt_of_eq_of_lt (OrientedCmp.eq_symm hbc) (OrientedCmp.lt_of_gt hab)) |>.symm

@[simp]
theorem lt_isLT : Ordering.lt.isLT := rfl

@[simp]
theorem lt_isLE : Ordering.lt.isLE := rfl

@[simp]
theorem lt_isEq : Ordering.lt.isEq = false := rfl

@[simp]
theorem lt_isGE : Ordering.lt.isGE = false := rfl

@[simp]
theorem lt_isGT : Ordering.lt.isGT = false := rfl

@[simp]
theorem eq_isLT : Ordering.eq.isLT = false := rfl

@[simp]
theorem eq_isLE : Ordering.eq.isLE := rfl

@[simp]
theorem eq_isEq : Ordering.eq.isEq := rfl

@[simp]
theorem eq_isGE : Ordering.eq.isGE := rfl

@[simp]
theorem eq_isGT : Ordering.eq.isGT = false := rfl

@[simp]
theorem gt_isLT : Ordering.gt.isLT = false := rfl

@[simp]
theorem gt_isLE : Ordering.gt.isLE = false := rfl

@[simp]
theorem gt_isEq : Ordering.gt.isEq = false := rfl

@[simp]
theorem gt_isGE : Ordering.gt.isGE := rfl

@[simp]
theorem gt_isGT : Ordering.gt.isGT := rfl

@[simp]
theorem lt_swap : Ordering.lt.swap = .gt := rfl

@[simp]
theorem eq_swap : Ordering.eq.swap = .eq := rfl

@[simp]
theorem gt_swap : Ordering.gt.swap = .lt := rfl

theorem TransCmp.eq_of_lt_of_lt [TransCmp cmp] {a b : α} (h₁ : cmp a b |>.isLE) (h₂ : cmp b a |>.isLE) :
    cmp a b = .eq := by
  rw [OrientedCmp.eq_swap (cmp := cmp)] at h₂
  cases h : cmp a b <;> rw [h] at h₁ h₂
  · simp at h₂
  · simp at h₁

end
