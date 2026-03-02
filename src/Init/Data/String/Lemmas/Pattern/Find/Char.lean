/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Find.Basic
import Init.Data.String.Lemmas.Pattern.Char
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate
import Init.Grind

namespace String.Slice

theorem find?_char_eq_some_iff {c : Char} {s : Slice} {pos : s.Pos} :
    s.find? c = some pos ↔
      ∃ h, pos.get h = c ∧ ∀ pos', (h' : pos' < pos) → pos'.get (Pos.ne_endPos_of_lt h') ≠ c := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.Char.matchesAt_iff]

@[simp]
theorem contains_char_eq {c : Char} {s : Slice} : s.contains c = decide (c ∈ s.copy.toList) := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp [Pattern.Model.Char.matchesAt_iff, mem_toList_copy_iff_exists_get]

end String.Slice
