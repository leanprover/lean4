/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.Classes
import Init.Data.Order.FactoriesExtra
import Init.Data.Order.Lemmas

public section

open Std

set_option linter.missingDocs true
set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

/-
Note: We're having verso docstrings disabled because the examples depend on instances that
are provided later in the module. They will be converted into verso docstrings at the end
of the module.
-/

/--
Inverts an {name}`LE` instance.

The result is an {lean}`LE α` instance where {lit}`a ≤ b` holds when {name}`le` would have
{lit}`b ≤ a` hold.

If {name}`le` obeys laws, then {lean}`le.opposite` obeys the opposite laws. For example, if
{name}`le` encodes a linear order, then {lean}`le.opposite` also encodes a linear order.
To automatically derive these laws, use {lit}`open Std.OppositeOrderInstances`.

For example, {name}`LE.opposite` can be used to derive maximum operations from minimum operations,
since finding the minimum in the opposite order is the same as finding the maximum in the original order:

```lean +warning
def min' [LE α] [DecidableLE α] (a b : α) : α :=
  if a ≤ b then a else b

open scoped Std.OppositeOrderInstances in
def max' [LE α] [DecidableLE α] (a b : α) : α :=
  letI : LE α := (inferInstanceAs (LE α)).opposite
  -- `DecidableLE` for the opposite order is derived automatically via `OppositeOrderInstances`
  min' a b
```

Without the `open scoped` command, Lean would not find the required {lit}`DecidableLE α`
instance for the opposite order.
-/
@[instance_reducible] def LE.opposite (le : LE α) : LE α where
  le a b := b ≤ a

theorem LE.opposite_def {le : LE α} :
    le.opposite = ⟨fun a b => b ≤ a⟩ :=
  (rfl)

theorem LE.le_opposite_iff {le : LE α} {a b : α} :
    (haveI := le.opposite; a ≤ b) ↔ b ≤ a := by
  exact Iff.rfl

/--
Inverts an {name}`LT` instance.

The result is an {lean}`LT α` instance where {lit}`a < b` holds when {name}`lt` would have
{lit}`b < a` hold.

If {name}`lt` obeys laws, then {lean}`lt.opposite` obeys the opposite laws.
To automatically derive these laws, use {lit}`open scoped Std.OppositeOrderInstances`.

For example, one can use the derived instances to prove properties about the opposite {name}`LT`
instance:

```lean
open scoped Std.OppositeOrderInstances in
example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] {x y : α} :
    letI : LE α := LE.opposite inferInstance
    letI : LT α := LT.opposite inferInstance
    ¬ y ≤ x ↔ x < y :=
  letI : LE α := LE.opposite inferInstance
  letI : LT α := LT.opposite inferInstance
  Std.not_le
```

Without the `open scoped` command, Lean would not find the {lit}`LawfulOrderLT α`
and {lit}`IsLinearOrder α` instances for the opposite order that are required by {name}`not_le`.
-/
def LT.opposite (lt : LT α) : LT α where
  lt a b := b < a

theorem LT.opposite_def {lt : LT α} :
    lt.opposite = ⟨fun a b => b < a⟩ :=
  (rfl)

theorem LT.lt_opposite_iff {lt : LT α} {a b : α} :
    (haveI := lt.opposite; a < b) ↔ b < a := by
  exact Iff.rfl

/--
Creates a {name}`Max` instance from a {name}`Min` instance.

The result is a {lean}`Max α` instance that uses {lean}`min.min` as its {name}`max` operation.

If {name}`min` obeys laws, then {lean}`min.oppositeMax` obeys the corresponding laws for {name}`Max`.
To automatically derive these laws, use {lit}`open scoped Std.OppositeOrderInstances`.

For example, one can use the derived instances to prove properties about the opposite {name}`Max`
instance:

```lean
open scoped Std.OppositeOrderInstances in
example [LE α] [DecidableLE α] [Min α] [Std.LawfulOrderLeftLeaningMin α] {a b : α} :
    letI : LE α := LE.opposite inferInstance
    letI : Max α := (inferInstance : Min α).oppositeMax
    max a b = if b ≤ a then a else b :=
  letI : LE α := LE.opposite inferInstance
  letI : Max α := (inferInstance : Min α).oppositeMax
  Std.max_eq_if
```

Without the `open scoped` command, Lean would not find the {lit}`LawfulOrderLeftLeaningMax α`
instance for the opposite order that is required by {name}`max_eq_if`.
-/
def Min.oppositeMax (min : Min α) : Max α where
  max a b := Min.min a b

theorem Min.oppositeMax_def {min : Min α} :
    min.oppositeMax = ⟨Min.min⟩ :=
  (rfl)

theorem Min.max_oppositeMax {min : Min α} {a b : α} :
    (haveI := min.oppositeMax; Max.max a b) = Min.min a b :=
  (rfl)

/--
Creates a {name}`Min` instance from a {name}`Max` instance.

The result is a {lean}`Min α` instance that uses {lean}`max.max` as its {name}`min` operation.

If {name}`max` obeys laws, then {lean}`max.oppositeMin` obeys the corresponding laws for {name}`Min`.
To automatically derive these laws, use {lit}`open scoped Std.OppositeOrderInstances`.

For example, one can use the derived instances to prove properties about the opposite {name}`Min`
instance:

```lean
open scoped Std.OppositeOrderInstances in
example [LE α] [DecidableLE α] [Max α] [Std.LawfulOrderLeftLeaningMax α] {a b : α} :
    letI : LE α := LE.opposite inferInstance
    letI : Min α := (inferInstance : Max α).oppositeMin
    min a b = if a ≤ b then a else b :=
  letI : LE α := LE.opposite inferInstance
  letI : Min α := (inferInstance : Max α).oppositeMin
  Std.min_eq_if
```

Without the `open scoped` command, Lean would not find the {lit}`LawfulOrderLeftLeaningMin α`
instance for the opposite order that is required by {name}`min_eq_if`.
-/
def Max.oppositeMin (max : Max α) : Min α where
  min a b := Max.max a b

theorem Max.oppositeMin_def {min : Max α} :
    min.oppositeMin = ⟨Max.max⟩ :=
  (rfl)

theorem Max.min_oppositeMin {max : Max α} {a b : α} :
    (haveI := max.oppositeMin; Min.min a b) = Max.max a b :=
  (rfl)

namespace Std.OppositeOrderInstances

@[no_expose]
scoped instance (priority := low) instDecidableLEOpposite {i : LE α} [id : DecidableLE α] :
    haveI := i.opposite
    DecidableLE α :=
  fun a b => id b a

@[no_expose]
scoped instance (priority := low) instDecidableLTOpposite {i : LT α} [id : DecidableLT α] :
    haveI := i.opposite
    DecidableLT α :=
  fun a b => id b a

scoped instance (priority := low) instLEReflOpposite {i : LE α} [Refl (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Refl (α := α) (· ≤ ·) :=
  letI := i.opposite
  { refl a := letI := i; le_refl a }

scoped instance (priority := low) instLESymmOpposite {i : LE α} [Symm (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Symm (α := α) (· ≤ ·) :=
  { symm a b hab := by
      simp [LE.le] at hab ⊢
      exact Symm.symm b a hab }

scoped instance (priority := low) instLEAntisymmOpposite {i : LE α} [Antisymm (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Antisymm (α := α) (· ≤ ·) :=
  { antisymm a b hab hba := by
      simp [LE.le] at hab hba
      exact le_antisymm hba hab }

scoped instance (priority := low) instLEAsymmOpposite {i : LE α} [Asymm (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Asymm (α := α) (· ≤ ·) :=
  { asymm a b hab := by
      simp [LE.le] at hab ⊢
      exact Asymm.asymm b a hab }

scoped instance (priority := low) instLETransOpposite {i : LE α}
    [Trans (· ≤ ·) (· ≤ ·) (· ≤ · : α → α → Prop)] :
    haveI := i.opposite
    Trans (· ≤ ·) (· ≤ ·) (· ≤ · : α → α → Prop) :=
  { trans hab hbc := by
      simp [LE.le] at hab hbc ⊢
      exact Trans.trans hbc hab }

scoped instance (priority := low) instLETotalOpposite {i : LE α} [Total (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Total (α := α) (· ≤ ·) :=
  letI := i.opposite
  { total a b := letI := i; le_total (a := b) (b := a) }

scoped instance (priority := low) instLEIrreflOpposite {i : LE α} [Irrefl (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Irrefl (α := α) (· ≤ ·) :=
  letI := i.opposite
  { irrefl a := letI := i; Irrefl.irrefl (r := (· ≤ ·)) a }

scoped instance (priority := low) instIsPreorderOpposite {i : LE α} [IsPreorder α] :
    haveI := i.opposite
    IsPreorder α :=
  letI := i.opposite
  { le_refl a := le_refl a
    le_trans _ _ _ := le_trans }

scoped instance (priority := low) instIsPartialOrderOpposite {i : LE α} [IsPartialOrder α] :
    haveI := i.opposite
    IsPartialOrder α :=
  letI := i.opposite
  { le_antisymm _ _ := le_antisymm }

scoped instance (priority := low) instIsLinearPreorderOpposite {i : LE α} [IsLinearPreorder α] :
    haveI := i.opposite
    IsLinearPreorder α :=
  letI := i.opposite
  { le_total _ _ := le_total }

scoped instance (priority := low) instIsLinearOrderOpposite {i : LE α} [IsLinearOrder α] :
    haveI := i.opposite
    IsLinearOrder α :=
  letI := i.opposite; {}

scoped instance (priority := low) instLawfulOrderOrdOpposite {il : LE α} {io : Ord α}
    [LawfulOrderOrd α] :
    haveI := il.opposite
    haveI := io.opposite
    LawfulOrderOrd α :=
  letI i := il.opposite
  letI j := io.opposite
  { isLE_compare a b := by
      unfold LE.opposite Ord.opposite
      simp only [compare, LE.le]
      letI := il; letI := io
      apply isLE_compare
    isGE_compare a b := by
      unfold LE.opposite Ord.opposite
      simp only [compare, LE.le]
      letI := il; letI := io
      apply isGE_compare }

scoped instance (priority := low) instLawfulOrderLTOpposite {il : LE α} {it : LT α}
    [LawfulOrderLT α] :
    haveI := il.opposite
    haveI := it.opposite
    LawfulOrderLT α :=
  letI := il.opposite
  letI := it.opposite
  { lt_iff a b := by
      letI := il; letI := it
      exact LawfulOrderLT.lt_iff b a }

scoped instance (priority := low) instLawfulOrderBEqOpposite {il : LE α} {ib : BEq α}
    [LawfulOrderBEq α] :
    haveI := il.opposite
    LawfulOrderBEq α :=
  letI := il.opposite
  { beq_iff_le_and_ge a b := by
      letI := il; letI := ib
      rw [LawfulOrderBEq.beq_iff_le_and_ge]
      exact and_comm }

scoped instance (priority := low) instLawfulOrderInfOpposite {il : LE α} {im : Min α}
    [LawfulOrderInf α] :
    haveI := il.opposite
    haveI := im.oppositeMax
    LawfulOrderSup α :=
  letI := il.opposite
  letI := im.oppositeMax
  { max_le_iff a b c := by
      letI := il; letI := im
      exact LawfulOrderInf.le_min_iff c a b }

scoped instance (priority := low) instLawfulOrderMinOpposite {il : LE α} {im : Min α}
    [LawfulOrderMin α] :
    haveI := il.opposite
    haveI := im.oppositeMax
    LawfulOrderMax α :=
  letI := il.opposite
  letI := im.oppositeMax
  { max_eq_or a b := by
      letI := il; letI := im
      exact MinEqOr.min_eq_or a b
    max_le_iff a b c := by
      letI := il; letI := im
      exact LawfulOrderInf.le_min_iff c a b }

scoped instance (priority := low) instLawfulOrderSupOpposite {il : LE α} {im : Max α}
    [LawfulOrderSup α] :
    haveI := il.opposite
    haveI := im.oppositeMin
    LawfulOrderInf α :=
  letI := il.opposite
  letI := im.oppositeMin
  { le_min_iff a b c := by
      letI := il; letI := im
      exact LawfulOrderSup.max_le_iff b c a }

scoped instance (priority := low) instLawfulOrderMaxOpposite {il : LE α} {im : Max α}
    [LawfulOrderMax α] :
    haveI := il.opposite
    haveI := im.oppositeMin
    LawfulOrderMin α :=
  letI := il.opposite
  letI := im.oppositeMin
  { min_eq_or a b := by
      letI := il; letI := im
      exact MaxEqOr.max_eq_or a b
    le_min_iff a b c := by
      letI := il; letI := im
      exact LawfulOrderSup.max_le_iff b c a }

scoped instance (priority := low) instLawfulOrderLeftLeaningMinOpposite {il : LE α} {im : Min α}
    [LawfulOrderLeftLeaningMin α] :
    haveI := il.opposite
    haveI := im.oppositeMax
    LawfulOrderLeftLeaningMax α :=
  letI := il.opposite
  letI := im.oppositeMax
  { max_eq_left a b hab := by
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMin.min_eq_left a b hab
    max_eq_right a b hab := by
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMin.min_eq_right a b hab }

scoped instance (priority := low) instLawfulOrderLeftLeaningMaxOpposite {il : LE α} {im : Max α}
    [LawfulOrderLeftLeaningMax α] :
    haveI := il.opposite
    haveI := im.oppositeMin
    LawfulOrderLeftLeaningMin α :=
  letI := il.opposite
  letI := im.oppositeMin
  { min_eq_left a b hab := by
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMax.max_eq_left a b hab
    min_eq_right a b hab := by
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMax.max_eq_right a b hab }

end OppositeOrderInstances

-- When imported from a non-module, these instances are exposed, and reducing them during
-- type class resolution is too inefficient.
attribute [irreducible] LE.opposite LT.opposite Min.oppositeMax Max.oppositeMin

section DocsToVerso

set_option linter.unusedVariables false -- Otherwise, we get warnings about Verso code blocks.
docs_to_verso LE.opposite
docs_to_verso LT.opposite
docs_to_verso Min.oppositeMax
docs_to_verso Max.oppositeMin

end DocsToVerso
