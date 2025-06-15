/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Consumers.Access
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Basic
import Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect

namespace Std.Iterators

theorem Iter.Equiv.toListRev_eq
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.toListRev = itb.toListRev := by
  simp [Iter.toListRev_eq_toListRev_toIterM, h.toIterM.toListRev_eq]

theorem Iter.Equiv.toList_eq
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.toList = itb.toList := by
  simp only [← Iter.reverse_toListRev, toListRev_eq h]

theorem Iter.Equiv.toArray_eq
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.toArray = itb.toArray := by
  simp only [← Iter.toArray_toList, toList_eq h]

end Std.Iterators
