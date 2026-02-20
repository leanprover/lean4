/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.Ord
public import Init.Data.Order.Classes
import Init.Data.Bool

namespace Std

/--
Creates an `LE α` instance from an `Ord α` instance.

`OrientedOrd α` must be satisfied so that the resulting `LE α` instance faithfully represents
the `Ord α` instance.
-/
@[inline, expose, implicit_reducible]
public def _root_.LE.ofOrd (α : Type u) [Ord α] : LE α where
  le a b := (compare a b).isLE

/--
Creates an `DecidableLE α` instance using a well-behaved `Ord α` instance.
-/
@[inline, expose]
public def _root_.DecidableLE.ofOrd (α : Type u) [LE α] [Ord α] [LawfulOrderOrd α] :
    DecidableLE α :=
  fun a b => match h : (compare a b).isLE with
    | true => isTrue (by simpa only [LawfulOrderOrd.isLE_compare] using h)
    | false => isFalse (by simpa only [LawfulOrderOrd.isLE_compare_eq_false] using h)

/--
Creates an `LT α` instance from an `Ord α` instance.

`OrientedOrd α` must be satisfied so that the resulting `LT α` instance faithfully represents
the `Ord α` instance.
-/
@[inline, expose, implicit_reducible]
public def _root_.LT.ofOrd (α : Type u) [Ord α] :
    LT α where
  lt a b := compare a b = .lt

public theorem isLE_compare {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α]
    {a b : α} : (compare a b).isLE ↔ a ≤ b := by
  simp [← LawfulOrderOrd.isLE_compare]

public theorem isGE_compare {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α]
    {a b : α} : (compare a b).isGE ↔ b ≤ a := by
  simp [← LawfulOrderOrd.isGE_compare]

-- We need to define `compare_eq_lt` and `compare_eq_gt` here instead of in `LemmasExtra.lean`
-- because they are needed for `DecidableLT.ofOrd`.
public theorem compare_eq_lt {α : Type u} [Ord α] [LT α] [LE α] [LawfulOrderOrd α] [LawfulOrderLT α]
    {a b : α} : compare a b = .lt ↔ a < b := by
  rw [LawfulOrderLT.lt_iff, ← LawfulOrderOrd.isLE_compare, ← LawfulOrderOrd.isGE_compare]
  cases compare a b <;> simp

public theorem compare_eq_gt {α : Type u} [Ord α] [LT α] [LE α] [LawfulOrderOrd α] [LawfulOrderLT α]
    {a b : α} : compare a b = .gt ↔ b < a := by
  rw [LawfulOrderLT.lt_iff, ← LawfulOrderOrd.isGE_compare, ← LawfulOrderOrd.isLE_compare]
  cases compare a b <;> simp

public theorem compare_eq_eq {α : Type u} [Ord α] [BEq α] [LE α] [LawfulOrderOrd α] [LawfulOrderBEq α]
    {a b : α} : compare a b = .eq ↔ a == b := by
  rw [LawfulOrderBEq.beq_iff_le_and_ge, ← isLE_compare, ← isGE_compare]
  cases compare a b <;> simp

public theorem compare_ne_eq {α : Type u} [Ord α] [BEq α] [LE α] [LawfulOrderOrd α] [LawfulOrderBEq α]
    {a b : α} :
    compare a b ≠ .eq ↔ ¬ a == b := by
  simp [compare_eq_eq]

public theorem compare_ne_eq_iff_ne {α : Type u} [Ord α] [LawfulEqOrd α] {a b : α} :
    compare a b ≠ .eq ↔ a ≠ b := by
  simp

grind_pattern compare_eq_lt => compare a b, Ordering.lt where
  guard compare a b = .lt

grind_pattern compare_eq_eq => compare a b, Ordering.eq where
  guard compare a b = .eq

grind_pattern compare_eq_gt => compare a b, Ordering.gt where
  guard compare a b = .gt

grind_pattern compare_ne_eq => compare a b, Ordering.eq where
  guard compare a b ≠ .eq

/--
Creates a `DecidableLT α` instance using a well-behaved `Ord α` instance.
-/
@[inline, expose]
public def _root_.DecidableLT.ofOrd (α : Type u) [LE α] [LT α] [Ord α] [LawfulOrderOrd α]
    [LawfulOrderLT α] :
    DecidableLT α :=
  fun a b => if h : compare a b = .lt then
      isTrue (by simpa only [compare_eq_lt] using h)
    else
      isFalse (by simpa only [compare_eq_lt] using h)

/--
Creates a `BEq α` instance from an `Ord α` instance. -/
@[inline, expose, implicit_reducible]
public def _root_.BEq.ofOrd (α : Type u) [Ord α] :
    BEq α where
  beq a b := compare a b = .eq

/--
The `LE α` instance obtained from an `Ord α` instance is compatible with said `Ord α`
instance if `compare` is oriented, i.e., `compare a b = .lt ↔ compare b a = .gt`.
-/
public instance instLawfulOrderOrd_ofOrd (α : Type u) [Ord α] [OrientedOrd α] :
    haveI := LE.ofOrd α
    LawfulOrderOrd α :=
  letI := LE.ofOrd α
  { isLE_compare := by simp [LE.le]
    isGE_compare := by simp [LE.le, OrientedCmp.isGE_eq_isLE] }

attribute [local instance] LT.ofOrd in
/--
The `LT α` instance obtained from an `Ord α` instance is compatible with the `LE α` instance
instance if `Ord α` is compatible with it.
-/
public instance instLawfulOrderLT_ofOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderLT α where
  lt_iff {a b} := by
    simp +contextual [LT.lt, ← Std.isLE_compare (a := a), ← Std.isGE_compare (a := a)]

attribute [local instance] BEq.ofOrd in
/--
The `BEq α` instance obtained from an `Ord α` instance is compatible with the `LE α` instance
instance if `Ord α` is compatible with it.
-/
public instance instLawfulOrderBEq_ofOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderBEq α where
  beq_iff_le_and_ge {a b} := by
    simp +contextual [BEq.beq, ← Std.isLE_compare (a := a), ← Std.isGE_compare (a := a),
      Ordering.eq_eq_iff_isLE_and_isGE]

end Std
