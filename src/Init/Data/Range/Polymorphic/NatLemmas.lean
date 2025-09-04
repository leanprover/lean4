/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Lemmas

public section

namespace Std.PRange.Nat

theorem succ_eq {n : Nat} : succ n = n + 1 :=
  rfl

theorem toList_Rco_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := by
  simp only [← succ_eq]
  rw [Std.PRange.toList_Rco_succ_succ_eq_map]

@[deprecated toList_Rco_succ_succ (since := "2025-08-22")]
theorem ClosedOpen.toList_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := toList_Rco_succ_succ

@[simp]
theorem Nat.size_Rco {a b : Nat} :
    (a...b).size = b - a := by
  simp [Std.PRange.size, Std.Iterators.Iter.size, Std.Iterators.IteratorSize.size,
    Std.PRange.Internal.iter, Std.Iterators.Iter.toIterM, Std.PRange.RangeSize.size]

@[simp]
theorem Nat.size_Rcc {a b : Nat} :
    (a...=b).size = b + 1- a := by
  simp [Std.PRange.size, Std.Iterators.Iter.size, Std.Iterators.IteratorSize.size,
    Std.PRange.Internal.iter, Std.Iterators.Iter.toIterM, Std.PRange.RangeSize.size]

end Std.PRange.Nat
