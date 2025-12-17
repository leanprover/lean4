/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Classes
public import Init.Data.Ord.Basic

namespace Std

/--
This typeclass states that the synthesized `Ord α` instance is compatible with the `LE α`
instance. This means that according to `compare`, the following are equivalent:

* `a` is less than or equal to `b` according to `compare`.
* `b` is greater than or equal to `b` according to `compare`.
* `a ≤ b` holds.

`LawfulOrderOrd α` automatically entails that `Ord α` is oriented (see `OrientedOrd α`)
and that `LE α` is total.

`Ord α` and `LE α` mutually determine each other in the presence of `LawfulOrderOrd α`.
-/
public class LawfulOrderOrd (α : Type u) [Ord α] [LE α] where
  isLE_compare : ∀ a b : α, (compare a b).isLE ↔ a ≤ b
  isGE_compare : ∀ a b : α, (compare a b).isGE ↔ b ≤ a

public theorem LawfulOrderOrd.isLE_compare_eq_false {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] {a b : α} :
    (compare a b).isLE = false ↔ ¬ a ≤ b := by
  simp [← isLE_compare]

public theorem LawfulOrderOrd.isGE_compare_eq_false {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] {a b : α} :
    (compare a b).isGE = false ↔ ¬ b ≤ a := by
  simp [← isGE_compare]

public abbrev LawfulOrderCmp (cmp : α → α → Ordering) [LE α] := @Std.LawfulOrderOrd α ⟨cmp⟩ _

end Std
