/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Range

@[expose] public section

namespace Std.PRange

@[simp]
theorem toList_iter_eq_toList [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [LawfulUpwardEnumerable α]
    (r : PRange ⟨sl, su⟩ α) :
    r.iter.toList = r.toList := by
 rfl

end Std.PRange
