/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Lemmas

namespace Option

@[simp] theorem mem_toList {a : α} {o : Option α} : a ∈ o.toList ↔ a ∈ o := by
  cases o <;> simp [eq_comm]

end Option
