/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Function
import Init.NotationExtra

public section

namespace Option

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intros a b hab
  cases a <;> cases b
  · simp
  · simp at hab
  · simp at hab
  · simp only [map_some, some.injEq] at hab
    simpa using hf hab

end Option
