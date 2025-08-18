/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.Ord

namespace Std

/--
Creates an `LE α` instance from an `Ord α` instance.

`OrientedOrd α` must be satisfied so that the resulting `LE α` instance faithfully represents
the `Ord α` instance.
-/
public def LE.ofOrd (α : Type u) [Ord α] : LE α where
  le a b := (compare a b).isLE

/--
The `LE α` instance obtained from an `Ord α` instance is compatible with said `Ord α`
instance if `compare` is oriented, i.e., `compare a b = .lt ↔ compare b a = .gt`.
-/
public instance LawfulOrderOrd.of_ord (α : Type u) [Ord α] [OrientedOrd α] :
    haveI := LE.ofOrd α
    LawfulOrderOrd α :=
  letI := LE.ofOrd α
  { isLE_compare := by simp [LE.ofOrd]
    isGE_compare := by simp [LE.ofOrd, OrientedCmp.isGE_eq_isLE] }

end Std
