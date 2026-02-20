/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Length
public import Init.Data.String.Modify
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Modify

public section

namespace String

@[simp]
theorem length_eq_zero_iff {s : String} : s.length = 0 ↔ s = "" := by
  simp [← length_toList]

@[simp]
theorem length_map {f : Char → Char} {s : String} : (s.map f).length = s.length := by
  simp [← length_toList]

end String
