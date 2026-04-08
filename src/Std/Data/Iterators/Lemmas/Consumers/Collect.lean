/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect

@[expose] public section

namespace Std
open Std.Iterators

theorem Iter.Equiv.toListRev_eq
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.toListRev = itb.toListRev := by
  simp [Iter.toListRev_eq_toListRev_toIterM, h.toIterM.toListRev_eq]

theorem Iter.Equiv.toList_eq
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.toList = itb.toList := by
  simp only [← Iter.reverse_toListRev, toListRev_eq h]

theorem Iter.Equiv.toArray_eq
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.toArray = itb.toArray := by
  simp only [← Iter.toArray_toList, toList_eq h]

end Std
