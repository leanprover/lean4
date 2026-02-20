/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
import Init.Data.Int.OfNat
import Init.Data.UInt.Lemmas
public import Init.Data.String

@[expose]
public section

/-!
# LowerCase

This module provides predicates and normalization functions for handling ASCII case-insensitivity.
It includes proofs of idempotency for lowercase transformations, as well as utilities for validating
the lowercase state of a String.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
Predicate asserting that a string is already in lowercase normal form.
-/
@[expose] def IsLowerCase (s : String) : Prop :=
  s.toLower = s

private theorem Char.toLower_eq_self_iff {c : Char} : c.toLower = c ↔ c.isUpper = false := by
  simp only [Char.toLower, Char.isUpper]
  split <;> rename_i h <;> simpa [UInt32.le_iff_toNat_le, Char.ext_iff] using h

private theorem String.toLower_eq_self_iff {s : String} : s.toLower = s ↔ s.toList.any Char.isUpper = false := by
  simp only [String.toLower, ← String.toList_inj, String.toList_map]
  rw (occs := [2]) [← List.map_id s.toList]
  rw [List.map_eq_map_iff]
  simp [Char.toLower_eq_self_iff]

instance : Decidable (IsLowerCase s) :=
  decidable_of_decidable_of_iff (p := s.toList.any Char.isUpper = false)
    (by exact String.toLower_eq_self_iff.symm)

namespace IsLowerCase

private theorem Char.toLower_idempotent (c : Char) : c.toLower.toLower = c.toLower := by
  grind [Char.toLower]

/--
Proof that applying `toLower` to any string results in a string that satisfies the `IsLowerCase`
predicate.
-/
theorem isLowerCase_toLower {s : String} : IsLowerCase s.toLower := by
  unfold IsLowerCase String.toLower
  rw [String.map_map, Function.comp_def]
  simp [Char.toLower_idempotent]

theorem isLowerCase_empty : IsLowerCase "" := by
  simp [IsLowerCase, String.toLower]

end Std.Http.Internal.IsLowerCase
