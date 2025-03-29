/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
prelude
import Init.Data.Ord
import Init.Data.SInt.Lemmas
import Init.Data.Vector.Lemmas

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

theorem ReflCmp.isLE_rfl {α} {cmp : α → α → Ordering} [ReflCmp cmp] {a : α} :
    (cmp a a).isLE := by
  simp [ReflCmp.compare_self (cmp := cmp)]

@[simp]
theorem ReflOrd.isLE_rfl {α} [Ord α] [ReflOrd α] {a : α} :
    (compare a a).isLE :=
  ReflCmp.isLE_rfl

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

theorem OrientedOrd.eq_swap [Ord α] [OrientedOrd α] {a b : α} :
    compare a b = (compare b a).swap := OrientedCmp.eq_swap

instance [OrientedCmp cmp] : ReflCmp cmp where
  compare_self := Ordering.eq_eq_of_eq_swap OrientedCmp.eq_swap

instance OrientedCmp.opposite [OrientedCmp cmp] : OrientedCmp fun a b => cmp b a where
  eq_swap := OrientedCmp.eq_swap (cmp := cmp)

instance OrientedOrd.opposite [Ord α] [OrientedOrd α] :
    letI : Ord α := .opposite inferInstance; OrientedOrd α :=
  OrientedCmp.opposite (cmp := compare)

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
    cmp a b = .lt → ¬ (cmp b a).isLE := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  simp

theorem OrientedCmp.not_isGE_of_gt [OrientedCmp cmp] {a b : α} :
    cmp a b = .gt → ¬ (cmp b a).isGE := by
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
    ¬ (cmp a b).isLE → cmp b a = .lt := by
  rw [OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp

theorem OrientedCmp.gt_of_not_isGE [OrientedCmp cmp] {a b : α} :
    ¬ (cmp a b).isGE → cmp b a = .gt := by
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

theorem TransOrd.isLE_trans [Ord α] [TransOrd α] {a b c : α} :
    (compare a b).isLE → (compare b c).isLE → (compare a c).isLE :=
  TransCmp.isLE_trans

theorem TransCmp.isGE_trans [TransCmp cmp] {a b c : α} (h₁ : (cmp a b).isGE) (h₂ : (cmp b c).isGE) :
    (cmp a c).isGE := by
  rw [OrientedCmp.isGE_iff_isLE] at *
  exact TransCmp.isLE_trans h₂ h₁

theorem TransOrd.isGE_trans [Ord α] [TransOrd α] {a b c : α} :
    (compare a b).isGE → (compare b c).isGE → (compare a c).isGE :=
  TransCmp.isGE_trans

instance TransCmp.opposite [TransCmp cmp] : TransCmp fun a b => cmp b a where
  isLE_trans := flip TransCmp.isLE_trans

instance TransOrd.opposite [Ord α] [TransOrd α] :
    letI : Ord α := .opposite inferInstance; TransOrd α :=
  TransCmp.opposite (cmp := compare)

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

theorem TransCmp.gt_of_gt_of_gt [TransCmp cmp] {a b c : α} (hab : cmp a b = .gt)
    (hbc : cmp b c = .gt) : cmp a c = .gt := by
  apply gt_of_gt_of_isGE hab (Ordering.isGE_of_eq_gt hbc)

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

theorem LawfulEqOrd.eq_of_compare [Ord α] [LawfulEqOrd α] {a b : α} :
    compare a b = .eq → a = b := LawfulEqCmp.eq_of_compare

instance LawfulEqCmp.opposite [OrientedCmp cmp] [LawfulEqCmp cmp] :
    LawfulEqCmp (fun a b => cmp b a) where
  eq_of_compare := by
    simp only [OrientedCmp.eq_comm (cmp := cmp)]
    exact LawfulEqCmp.eq_of_compare

instance LawfulEqOrd.opposite [Ord α] [OrientedOrd α] [LawfulEqOrd α] :
    letI : Ord α := .opposite inferInstance; LawfulEqOrd α :=
  LawfulEqCmp.opposite (cmp := compare)

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

instance LawfulBEqCmp.opposite [OrientedCmp cmp] [LawfulBEqCmp cmp] :
    LawfulBEqCmp (fun a b => cmp b a) where
  compare_eq_iff_beq := by
    simp [OrientedCmp.eq_comm (cmp := cmp), LawfulBEqCmp.compare_eq_iff_beq]

instance LawfulBEqOrd.opposite [Ord α] [OrientedOrd α] [LawfulBEqOrd α] :
    letI : Ord α := .opposite inferInstance; LawfulBEqOrd α :=
  LawfulBEqCmp.opposite (cmp := compare)

end LawfulBEq

namespace Internal

variable {α : Type u}

/--
Internal funcion to derive a `BEq` instance from an `Ord` instance in order to connect the
verification machinery for tree maps to the verification machinery for hash maps.
-/
@[local instance]
def beqOfOrd [Ord α] : BEq α where
  beq a b := compare a b = .eq

instance {_ : Ord α} : LawfulBEqOrd α where
  compare_eq_iff_beq {a b} := by simp only [beqOfOrd, decide_eq_true_eq]

@[local simp]
theorem beq_eq [Ord α] {a b : α} : (a == b) = (compare a b = .eq) := by
  rw [compare_eq_iff_beq]

theorem beq_iff [Ord α] {a b : α} : (a == b) = true ↔ compare a b = .eq :=
  eq_iff_iff.mp beq_eq

theorem eq_beqOfOrd_of_lawfulBEqOrd [Ord α] (inst : BEq α) [instLawful : LawfulBEqOrd α] :
    inst = beqOfOrd := by
  cases inst; rename_i instBEq
  congr; ext a b
  rw [Bool.eq_iff_iff, decide_eq_true_eq, instLawful.compare_eq_iff_beq]
  rfl

theorem equivBEq_of_transOrd [Ord α] [TransOrd α] : EquivBEq α where
  symm {a b} h := by simp_all [OrientedCmp.eq_comm]
  trans h₁ h₂ := by simp_all only [beq_eq, beq_iff_eq]; exact TransCmp.eq_trans h₁ h₂
  refl := by simp only [beq_eq, beq_iff_eq]; exact compare_self

theorem lawfulBEq_of_lawfulEqOrd [Ord α] [LawfulEqOrd α] : LawfulBEq α where
  eq_of_beq hbeq := by simp_all
  rfl := by simp

end Internal

section Instances

theorem TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff
    {α : Type u} [LT α] [DecidableLT α] [DecidableEq α]
    (lt_trans : ∀ {a b c : α}, a < b → b < c → a < c)
    (h : ∀ x y : α, x < y ↔ ¬ y < x ∧ x ≠ y) :
    TransCmp (fun x y : α => compareOfLessAndEq x y) where
  eq_swap := compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne h
  isLE_trans {x y z} h₁ h₂ := by
    simp only [compare, compareOfLessAndEq, apply_ite Ordering.isLE,
      Ordering.isLE_lt, Ordering.isLE_eq, Ordering.isLE_gt] at h₁ h₂ ⊢
    simp only [Bool.if_true_left, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
    rcases h₁ with (h₁ | rfl)
    · rcases h₂ with (h₂ | rfl)
      · exact .inl (lt_trans h₁ h₂)
      · exact .inl h₁
    · exact h₂

theorem TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableLE α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (trans : ∀ {x y z : α}, x ≤ y → y ≤ z → x ≤ z) (total : ∀ (x y : α), x ≤ y ∨ y ≤ x)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) :
    TransCmp (fun x y : α => compareOfLessAndEq x y) := by
  refine compareOfLessAndEq_of_lt_trans_of_lt_iff ?_ ?_
  · intro a b c
    simp only [← not_le]
    intro h₁ h₂ h₃
    replace h₁ := (total _ _).resolve_left h₁
    exact h₂ (trans h₃ h₁)
  · exact lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le antisymm total not_le

namespace Bool

instance : TransOrd Bool where
  eq_swap {x y} := by cases x <;> cases y <;> rfl
  isLE_trans {x y z} h₁ h₂ := by cases x <;> cases y <;> cases z <;> trivial

instance : LawfulEqOrd Bool where
  eq_of_compare {x y} := by cases x <;> cases y <;> simp

end Bool

namespace Nat

instance : TransOrd Nat :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Nat.le_antisymm Nat.le_trans Nat.le_total Nat.not_le

instance : LawfulEqOrd Nat where
  eq_of_compare := compareOfLessAndEq_eq_eq Nat.le_refl Nat.not_le |>.mp

end Nat

namespace Int

instance : TransOrd Int :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int.le_antisymm Int.le_trans Int.le_total Int.not_le

instance : LawfulEqOrd Int where
  eq_of_compare := compareOfLessAndEq_eq_eq Int.le_refl Int.not_le |>.mp

end Int

namespace Fin

variable (n : Nat)

instance : OrientedOrd (Fin n) where
  eq_swap := OrientedOrd.eq_swap (α := Nat)

instance : TransOrd (Fin n) where
  isLE_trans := TransOrd.isLE_trans (α := Nat)

instance : LawfulEqOrd (Fin n) where
  eq_of_compare h := Fin.eq_of_val_eq <| LawfulEqOrd.eq_of_compare h

end Fin

namespace String

instance : TransOrd String :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    String.le_antisymm String.le_trans String.le_total String.not_le

instance : LawfulEqOrd String where
  eq_of_compare h := compareOfLessAndEq_eq_eq String.le_refl String.not_le |>.mp h

end String

namespace Char

instance : TransOrd Char :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Char.le_antisymm Char.le_trans Char.le_total Char.not_le

instance : LawfulEqOrd Char where
  eq_of_compare h := compareOfLessAndEq_eq_eq Char.le_refl Char.not_le |>.mp h

end Char

namespace UInt8

instance : TransOrd UInt8 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    UInt8.le_antisymm UInt8.le_trans UInt8.le_total UInt8.not_le

instance : LawfulEqOrd UInt8 where
  eq_of_compare h := compareOfLessAndEq_eq_eq UInt8.le_refl UInt8.not_le |>.mp h

end UInt8

namespace UInt16

instance : TransOrd UInt16 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    UInt16.le_antisymm UInt16.le_trans UInt16.le_total UInt16.not_le

instance : LawfulEqOrd UInt16 where
  eq_of_compare h := compareOfLessAndEq_eq_eq UInt16.le_refl UInt16.not_le |>.mp h

end UInt16

namespace UInt32

instance : TransOrd UInt32 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    UInt32.le_antisymm UInt32.le_trans UInt32.le_total UInt32.not_le

instance : LawfulEqOrd UInt32 where
  eq_of_compare h := compareOfLessAndEq_eq_eq UInt32.le_refl UInt32.not_le |>.mp h

end UInt32

namespace UInt64

instance : TransOrd UInt64 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    UInt64.le_antisymm UInt64.le_trans UInt64.le_total UInt64.not_le

instance : LawfulEqOrd UInt64 where
  eq_of_compare h := compareOfLessAndEq_eq_eq UInt64.le_refl UInt64.not_le |>.mp h

end UInt64

namespace USize

instance : TransOrd USize :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    USize.le_antisymm USize.le_trans USize.le_total USize.not_le

instance : LawfulEqOrd USize where
  eq_of_compare h := compareOfLessAndEq_eq_eq USize.le_refl USize.not_le |>.mp h

end USize

namespace Int8

instance : TransOrd Int8 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int8.le_antisymm Int8.le_trans Int8.le_total Int8.not_le

instance : LawfulEqOrd Int8 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int8.le_refl Int8.not_le |>.mp h

end Int8

namespace Int16

instance : TransOrd Int16 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int16.le_antisymm Int16.le_trans Int16.le_total Int16.not_le

instance : LawfulEqOrd Int16 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int16.le_refl Int16.not_le |>.mp h

end Int16

namespace Int32

instance : TransOrd Int32 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int32.le_antisymm Int32.le_trans Int32.le_total Int32.not_le

instance : LawfulEqOrd Int32 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int32.le_refl Int32.not_le |>.mp h

end Int32

namespace Int64

instance : TransOrd Int64 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int64.le_antisymm Int64.le_trans Int64.le_total Int64.not_le

instance : LawfulEqOrd Int64 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int64.le_refl Int64.not_le |>.mp h

end Int64

namespace ISize

instance : TransOrd ISize :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    ISize.le_antisymm ISize.le_trans ISize.le_total ISize.not_le

instance : LawfulEqOrd ISize where
  eq_of_compare h := compareOfLessAndEq_eq_eq ISize.le_refl ISize.not_le |>.mp h

end ISize

namespace BitVec

variable {n : Nat}

instance : TransOrd (BitVec n) :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    BitVec.le_antisymm BitVec.le_trans BitVec.le_total BitVec.not_le

instance : LawfulEqOrd (BitVec n) where
  eq_of_compare h := compareOfLessAndEq_eq_eq BitVec.le_refl BitVec.not_le |>.mp h

end BitVec

namespace Option

instance {α} [Ord α] [OrientedOrd α] : OrientedOrd (Option α) where
  eq_swap {a b} := by cases a <;> cases b <;> simp [Ord.compare, ← OrientedOrd.eq_swap]

instance {α} [Ord α] [TransOrd α] : TransOrd (Option α) where
  isLE_trans {a b c} hab hbc := by
    cases a <;> cases b <;> cases c <;> (try simp_all [Ord.compare]; done)
    simp only [Ord.compare] at *
    apply TransOrd.isLE_trans <;> assumption

instance {α} [Ord α] [ReflOrd α] : ReflOrd (Option α) where
  compare_self {a} := by cases a <;> simp [Ord.compare]

instance {α} [Ord α] [LawfulEqOrd α] : LawfulEqOrd (Option α) where
  eq_of_compare {a b} := by
    cases a <;> cases b <;> simp_all [Ord.compare, LawfulEqOrd.eq_of_compare]

instance {α} [Ord α] [BEq α] [LawfulBEqOrd α] : LawfulBEqOrd (Option α) where
  compare_eq_iff_beq {a b} := by
    cases a <;> cases b <;> simp_all [Ord.compare, LawfulBEqOrd.compare_eq_iff_beq]

end Option

section Lex

instance {α} {cmp₁ cmp₂} [ReflCmp cmp₁] [ReflCmp cmp₂] :
    ReflCmp (α := α) (compareLex cmp₁ cmp₂) where
  compare_self {a} := by simp [compareLex, ReflCmp.compare_self]

instance {α} {cmp₁ cmp₂} [OrientedCmp cmp₁] [OrientedCmp cmp₂] :
    OrientedCmp (α := α) (compareLex cmp₁ cmp₂) where
  eq_swap {a b} := by
    rw [compareLex, compareLex, OrientedCmp.eq_swap (cmp := cmp₁) (a := b), Ordering.swap_then,
      Ordering.swap_swap, ← OrientedCmp.eq_swap]

instance {α} {cmp₁ cmp₂} [TransCmp cmp₁] [TransCmp cmp₂] :
    TransCmp (α := α) (compareLex cmp₁ cmp₂) where
  isLE_trans {a b c} hab hbc := by
    simp only [compareLex] at *
    simp only [Ordering.isLE_then_iff_and] at *
    refine ⟨TransCmp.isLE_trans hab.1 hbc.1, ?_⟩
    cases hab.2
    case inl hab' => exact Or.inl <| TransCmp.lt_of_lt_of_isLE hab' hbc.1
    case inr hab' =>
      cases hbc.2
      case inl hbc' => exact Or.inl <| TransCmp.lt_of_isLE_of_lt hab.1 hbc'
      case inr hbc' => exact Or.inr <| TransCmp.isLE_trans hab' hbc'

instance {α β} {f : α → β} [Ord β] [ReflOrd β] :
    ReflCmp (compareOn f) where
  compare_self := ReflOrd.compare_self (α := β)

instance {α β} {f : α → β} [Ord β] [OrientedOrd β] :
    OrientedCmp (compareOn f) where
  eq_swap := OrientedOrd.eq_swap (α := β)

instance {α β} {f : α → β} [Ord β] [TransOrd β] :
    TransCmp (compareOn f) where
  isLE_trans := TransOrd.isLE_trans (α := β)

attribute [instance] lexOrd in
instance {α β} [Ord α] [Ord β] [ReflOrd α] [ReflOrd β] :
    ReflOrd (α × β) :=
  inferInstanceAs <| ReflCmp (compareLex _ _)

attribute [instance] lexOrd in
instance {α β} [Ord α] [Ord β] [OrientedOrd α] [OrientedOrd β] :
    OrientedOrd (α × β) :=
  inferInstanceAs <| OrientedCmp (compareLex _ _)

attribute [instance] lexOrd in
instance {α β} [Ord α] [Ord β] [TransOrd α] [TransOrd β] :
    TransOrd (α × β) :=
  inferInstanceAs <| TransCmp (compareLex _ _)

attribute [instance] lexOrd in
instance {α β} [Ord α] [Ord β] [LawfulEqOrd α] [LawfulEqOrd β] : LawfulEqOrd (α × β) where
  eq_of_compare {a b} h := by
    simp only [lexOrd, compareLex_eq_eq, compareOn] at h
    ext
    · exact LawfulEqOrd.eq_of_compare h.1
    · exact LawfulEqOrd.eq_of_compare h.2

end Lex

end Instances

end Std

namespace List

open Std

variable {α} {cmp : α → α → Ordering}

instance [ReflCmp cmp] : ReflCmp (List.compareLex cmp) where
  compare_self {a} := by
    induction a with
    | nil => rfl
    | cons x xs h =>
      simp [List.compareLex_cons_cons, Ordering.then_eq_eq, ReflCmp.compare_self, h]

instance [LawfulEqCmp cmp] : LawfulEqCmp (List.compareLex cmp) where
  eq_of_compare {a b} h := by
    induction a generalizing b with
    | nil => simpa [List.compareLex_nil_left_eq_eq] using h
    | cons x xs ih =>
      cases b
      · simp [List.compareLex_nil_right_eq_eq] at h
      · simp only [List.compareLex_cons_cons, Ordering.then_eq_eq, compare_eq_iff_eq,
        List.cons.injEq] at *
        exact ⟨h.1, ih h.2⟩

instance [BEq α] [LawfulBEqCmp cmp] : LawfulBEqCmp (List.compareLex cmp) where
  compare_eq_iff_beq {a b} := by
    induction a generalizing b with
    | nil => simp [List.compareLex_nil_left_eq_eq]
    | cons x xs ih =>
      cases b
      · simp [List.compareLex_cons_nil]
      · simp [List.compareLex_cons_cons, Ordering.then_eq_eq, LawfulBEqCmp.compare_eq_iff_beq, ih]

instance [OrientedCmp cmp] : OrientedCmp (List.compareLex cmp) where
  eq_swap {a b} := by
    induction a generalizing b with
    | nil =>
      cases b
      · simp [List.compareLex_nil_nil]
      · simp [List.compareLex_nil_cons, List.compareLex_cons_nil]
    | cons x xs ih =>
      cases b
      · simp [List.compareLex_nil_cons, List.compareLex_cons_nil]
      · simp [OrientedCmp.eq_swap (a := x), List.compareLex_cons_cons, ih, Ordering.swap_then]

instance [TransCmp cmp] : TransCmp (List.compareLex cmp) where
  isLE_trans {a b c} (hab hbc) := by
    induction a generalizing b c with
    | nil => exact List.isLE_compareLex_nil_left
    | cons _ _ ih =>
      cases b <;> cases c <;> (try simp [List.compareLex_cons_nil] at *; done)
      simp only [List.compareLex_cons_cons, Ordering.isLE_then_iff_and] at *
      apply And.intro
      · exact TransCmp.isLE_trans hab.1 hbc.1
      · obtain ⟨hable, (hab | hab)⟩ := hab
        · exact Or.inl <| TransCmp.lt_of_lt_of_isLE hab hbc.1
        · obtain ⟨_, (hbc | hbc)⟩ := hbc
          · exact Or.inl <| TransCmp.lt_of_isLE_of_lt hable hbc
          · exact Or.inr <| ih hab hbc

instance [Ord α] [ReflOrd α] : ReflOrd (List α) :=
  inferInstanceAs <| ReflCmp (List.compareLex compare)

instance [Ord α] [LawfulEqOrd α] : LawfulEqOrd (List α) :=
  inferInstanceAs <| LawfulEqCmp (List.compareLex compare)

instance [Ord α] [BEq α] [LawfulBEqOrd α] : LawfulBEqOrd (List α) :=
  inferInstanceAs <| LawfulBEqCmp (List.compareLex compare)

instance [Ord α] [OrientedOrd α] : OrientedOrd (List α) :=
  inferInstanceAs <| OrientedCmp (List.compareLex compare)

instance [Ord α] [TransOrd α] : TransOrd (List α) :=
  inferInstanceAs <| TransCmp (List.compareLex compare)

end List

namespace Array

open Std

variable {α} {cmp : α → α → Ordering}

instance [ReflCmp cmp] : ReflCmp (Array.compareLex cmp) where
  compare_self {a} := by simp [Array.compareLex_eq_compareLex_toList, ReflCmp.compare_self]

instance [LawfulEqCmp cmp] : LawfulEqCmp (Array.compareLex cmp) where
  eq_of_compare {a b} := by
    simp only [Array.compareLex_eq_compareLex_toList, compare_eq_iff_eq]
    exact congrArg List.toArray

instance [BEq α] [LawfulBEqCmp cmp] : LawfulBEqCmp (Array.compareLex cmp) where
  compare_eq_iff_beq {a b} := by
    simp only [Array.compareLex_eq_compareLex_toList, BEq.beq, ← Array.isEqv_toList,
      LawfulBEqCmp.compare_eq_iff_beq, List.beq_eq_isEqv]

instance [OrientedCmp cmp] : OrientedCmp (Array.compareLex cmp) where
  eq_swap {a b} := by simp [Array.compareLex_eq_compareLex_toList, ← OrientedCmp.eq_swap]

instance [TransCmp cmp] : TransCmp (Array.compareLex cmp) where
  isLE_trans {a b c} hab hac := by
    simp only [Array.compareLex_eq_compareLex_toList] at *
    exact TransCmp.isLE_trans hab hac

instance [Ord α] [ReflOrd α] : ReflOrd (Array α) :=
  inferInstanceAs <| ReflCmp (Array.compareLex compare)

instance [Ord α] [LawfulEqOrd α] : LawfulEqOrd (Array α) :=
  inferInstanceAs <| LawfulEqCmp (Array.compareLex compare)

instance [Ord α] [BEq α] [LawfulBEqOrd α] : LawfulBEqOrd (Array α) :=
  inferInstanceAs <| LawfulBEqCmp (Array.compareLex compare)

instance [Ord α] [OrientedOrd α] : OrientedOrd (Array α) :=
  inferInstanceAs <| OrientedCmp (Array.compareLex compare)

instance [Ord α] [TransOrd α] : TransOrd (Array α) :=
  inferInstanceAs <| TransCmp (Array.compareLex compare)

end Array

namespace Vector

open Std

variable {α} {cmp : α → α → Ordering}

instance [ReflCmp cmp] {n} : ReflCmp (Vector.compareLex cmp (n := n)) where
  compare_self := ReflCmp.compare_self (cmp := Array.compareLex cmp)

instance [LawfulEqCmp cmp] {n} : LawfulEqCmp (Vector.compareLex cmp (n := n)) where
  eq_of_compare := by simp [Vector.compareLex_eq_compareLex_toArray]

instance [BEq α] [LawfulBEqCmp cmp] {n} : LawfulBEqCmp (Vector.compareLex cmp (n := n)) where
  compare_eq_iff_beq := by simp [Vector.compareLex_eq_compareLex_toArray,
    LawfulBEqCmp.compare_eq_iff_beq]

instance [OrientedCmp cmp] {n} : OrientedCmp (Vector.compareLex cmp (n := n)) where
  eq_swap := OrientedCmp.eq_swap (cmp := Array.compareLex cmp)

instance [TransCmp cmp] {n} : TransCmp (Vector.compareLex cmp (n := n)) where
  isLE_trans := TransCmp.isLE_trans (cmp := Array.compareLex cmp)

instance [Ord α] [ReflOrd α] {n} : ReflOrd (Vector α n) :=
  inferInstanceAs <| ReflCmp (Vector.compareLex compare)

instance [Ord α] [LawfulEqOrd α] {n} : LawfulEqOrd (Vector α n) :=
  inferInstanceAs <| LawfulEqCmp (Vector.compareLex compare)

instance [Ord α] [BEq α] [LawfulBEqOrd α] {n} : LawfulBEqOrd (Vector α n) :=
  inferInstanceAs <| LawfulBEqCmp (Vector.compareLex compare)

instance [Ord α] [OrientedOrd α] {n} : OrientedOrd (Vector α n) :=
  inferInstanceAs <| OrientedCmp (Vector.compareLex compare)

instance [Ord α] [TransOrd α] {n} : TransOrd (Vector α n) :=
  inferInstanceAs <| TransCmp (Vector.compareLex compare)

end Vector
