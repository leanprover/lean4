/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Monadic.Take

namespace Std.Iterators

@[always_inline, inline]
def Iter.take {α : Type w} {β : Type w} (n : Nat) (it : Iter (α := α) β) :
    Iter (α := Take α Id β) β :=
  it.toIterM.take n |>.toIter

end Std.Iterators
