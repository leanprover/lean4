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
Creates an `OrderData α` instance from an `Ord α` instance.

As `OrderData α` is encoded as a mere less-than-or-equal relation, `OrientedOrd α` must be satisfied
so that the resulting `OrderData α` instance faithfully represents the `Ord α` instance.
-/
public def OrderData.ofOrd (α : Type u) [Ord α] : OrderData α where
  IsLE a b := (compare a b).isLE

/--
The `OrderData α` instance obtained from an `Ord α` instance is compatible with said `Ord α`
instance if `compare` is oriented, i.e., `compare a b = .lt ↔ compare b a = .gt`.
-/
public instance LawfulOrderOrd.ofOrd (α : Type u) [Ord α] [OrientedOrd α] :
    haveI : OrderData α := .ofOrd α
    LawfulOrderOrd α :=
  letI : OrderData α := .ofOrd α
  { compare_isLE := by simp [OrderData.ofOrd]
    compare_isGE := by simp [OrientedCmp.isGE_iff_isLE, OrderData.ofOrd] }

end Std
