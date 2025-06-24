/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Basic

namespace Std.Iterators

/--
A wrapper around an iterator that provides partial consumers. See `IterM.allowNontermination`.
-/
structure IterM.Partial {α : Type w} (m : Type w → Type w') (β : Type w) where
  it : IterM (α := α) m β

/--
For an iterator `it`, `it.allowNontermination` provides potentially nonterminating variants of
consumers such as `toList`. They can be used without any proof of termination such as `Finite`
or `Productive`, but as they are implemented with the `partial` declaration modifier, they are
opaque for the kernel and it is impossible to prove anything about them.
-/
@[always_inline, inline]
def IterM.allowNontermination {α : Type w} {m : Type w → Type w'} {β : Type w}
    (it : IterM (α := α) m β) : IterM.Partial (α := α) m β :=
  ⟨it⟩

end Std.Iterators
