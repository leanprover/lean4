/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
import Init.Data.Array.Lemmas
import Init.Data.Option.List

namespace Option

@[simp]
theorem toList_toArray {o : Option α} : o.toArray.toList = o.toList := by
  cases o <;> simp

@[simp]
theorem toArray_toList {o : Option α} : o.toList.toArray = o.toArray := by
  cases o <;> simp

theorem toArray_filter {o : Option α} {p : α → Bool} :
    (o.filter p).toArray = o.toArray.filter p := by
  rw [← toArray_toList, toList_filter, ← List.filter_toArray, toArray_toList]

end Option
