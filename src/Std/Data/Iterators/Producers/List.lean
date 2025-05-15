/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Producers.Monadic.List

namespace Std.Iterators

@[always_inline, inline]
def _root_.List.iter {α : Type w} (l : List α) :
    Iter (α := ListIterator α) α :=
  ((l.iterM Id).toPureIter : Iter α)

end Std.Iterators
