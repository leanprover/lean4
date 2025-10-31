/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic

/-!
# Basic lemmas about strings

This file contains lemmas that could be in `Init.Data.String.Basic` but are not because they are
not needed to define basic string operations.
-/

public section

namespace String

@[simp]
theorem singleton_append_inj : singleton c ++ s = singleton d ++ t ↔ c = d ∧ s = t := by
  simp [← toList_inj]

@[simp]
theorem push_inj : push s c = push t d ↔ s = t ∧ c = d := by
  simp [← toList_inj]

end String
