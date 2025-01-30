/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.OrderAxioms.ReflOrd

set_option autoImplicit false
set_option linter.missingDocs true

universe u

/--
The `LawfulEqOrd` typeclass says that `compare a b = .eq` if and only if the logical equality
`a = b` holds.
-/
class LawfulEqOrd (α : Type u) [Ord α] extends ReflOrd α : Prop where
  /-- If two values compare equal, then they are logically equal. -/
  eq_of_compare {a b : α} : compare a b = .eq → a = b

export LawfulEqOrd (eq_of_compare)

variable {α : Type u} [Ord α] [LawfulEqOrd α]

@[simp]
theorem compare_eq_iff_eq {a b : α} : compare a b = .eq ↔ a = b :=
  ⟨LawfulEqOrd.eq_of_compare, by rintro rfl; simp⟩
