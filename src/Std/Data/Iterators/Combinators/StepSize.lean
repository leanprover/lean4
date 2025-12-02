/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.Monadic.StepSize

@[expose] public section

/-!
This module provides a combinator that only yields every `n`-th element of another iterator.
-/

namespace Std
open Std.Iterators

@[always_inline, inline, inherit_doc IterM.stepSize]
def Iter.stepSize [Iterator α Id β] [IteratorAccess α Id]
    (it : Iter (α := α) β) (n : Nat) :
    Iter (α := Types.StepSizeIterator α Id β) β :=
  (it.toIterM.stepSize n).toIter

end Std
