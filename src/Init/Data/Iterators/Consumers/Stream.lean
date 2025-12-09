/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Stream
public import Init.Data.Iterators.Consumers.Access
import all Init.Data.Iterators.Consumers.Monadic.Access

public section

namespace Std.Iterators

instance {α β} [Iterator α Id β] [Productive α Id]
    [IteratorAccess α Id] [LawfulIteratorAccess α Id] :
    Stream (Iter (α := α) β) β where
  next? it := match h : (it.toIterM.nextAtIdx? 0).run with
    | .yield it' out => some (out, it'.toIter)
    | .skip it' => False.elim ?noskip
    | .done => none
  where finally
    case noskip =>
      revert h
      have := IterM.not_isPlausibleNthOutputStep_skip (α := α) (m := Id) (it := it.toIterM) (it' := it') (n := 0)
      replace := this.imp LawfulIteratorAccess.isPlausibleNthOutputStep_of_canReturn
      exact this

end Std.Iterators
