/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Attach
public import Init.Data.Iterators.Combinators.FilterMap

public section

namespace Std.Iterators

@[always_inline, inline, expose, inherit_doc IterM.attachWith]
def Iter.attachWith {α β : Type w}
    [Iterator α Id β]
    (it : Iter (α := α) β) (P : β → Prop) (h : ∀ out, it.IsPlausibleIndirectOutput out → P out) :
  Iter (α := Types.Attach α Id P) { out : β // P out } :=
  (it.toIterM.attachWith P ?h).toIter
where finally
  case h =>
    simp only [← isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
    exact h

end Std.Iterators
