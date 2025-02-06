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
The `LawfulEqCmp cmp` typeclass says `cmp a b = .eq` if and only if the logical equality
`a = b` holds.
-/
class LawfulEqCmp {α : Type u} (cmp : α → α → Ordering) extends ReflCmp cmp : Prop where
  /-- If two values compare equal, then they are logically equal. -/
  eq_of_compare {a b : α} : cmp a b == .eq → a = b

/--
The `LawfulEqOrd` typeclass says that `compare a b = .eq` if and only if the logical equality
`a = b` holds.
-/
abbrev LawfulEqOrd (α : Type u) [Ord α] := LawfulEqCmp (compare : α → α → Ordering)

variable {α : Type u} {cmp : α → α → Ordering} [LawfulEqCmp cmp]

@[simp]
theorem compare_eq_iff_eq {a b : α} : cmp a b = .eq ↔ a = b :=
  ⟨LawfulEqCmp.eq_of_compare ∘ beq_of_eq, by rintro rfl; simp⟩

@[simp]
theorem compare_beq_iff_eq {a b : α} : cmp a b == .eq ↔ a = b :=
  ⟨LawfulEqCmp.eq_of_compare, by rintro rfl; simp⟩
