/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude

public import Init.Data.String.Basic
import Init.Data.String.Lemmas.Iterate
import Init.Data.Iterators.Lemmas.Consumers.Collect

/-!
This module contains `csimp` lemmas used to optimize `String` functions.
-/

public section

namespace String

def toListImpl (s : String) : List Char := s.revChars.toListRev

@[csimp]
theorem toList_eq_toListImpl : @toList = @toListImpl := by
  funext
  simp [toListImpl, Std.Iter.toListRev_eq]

end String
