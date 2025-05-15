/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Basic

namespace Std.Iterators

structure IterM.Partial {α : Type w} (m : Type w → Type w') (β : Type v) where
  it : IterM (α := α) m β

@[always_inline, inline]
def IterM.allowNontermination {α : Type w} {m : Type w → Type w'} {β : Type w}
    (it : IterM (α := α) m β) : IterM.Partial (α := α) m β :=
  ⟨it⟩

end Std.Iterators
