/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Search
import all Init.Data.String.Search

public section

namespace String
open Std String.Slice Pattern

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.IteratorLoop (σ s) Id Id]

@[simp]
theorem Slice.Pos.le_find {s : Slice} (pos : s.Pos) (pattern : ρ) [ToForwardSearcher pattern σ] :
    pos ≤ pos.find pattern := by
  simp [Slice.Pos.find]

@[simp]
theorem Pos.le_find {s : String} (pos : s.Pos) (pattern : ρ) [ToForwardSearcher pattern σ] :
    pos ≤ pos.find pattern := by
  simp [Pos.find, ← toSlice_le]

end String
