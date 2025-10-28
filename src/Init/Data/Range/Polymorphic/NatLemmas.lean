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
  rw [Std.Rco.toList_succ_succ_eq_map]

@[deprecated toList_Rco_succ_succ (since := "2025-08-22")]
theorem ClosedOpen.toList_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := toList_Rco_succ_succ

@[simp]
theorem size_Rcc {a b : Nat} :
    (a...=b).size = b + 1 - a := by
  simp [Rcc.size, Rxc.HasSize.size]

@[simp]
theorem size_Rco {a b : Nat} :
    (a...b).size = b - a := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[simp]
theorem size_Roc {a b : Nat} :
    (a<...=b).size = b - a := by
  simp [Roc.size, Rxc.HasSize.size]

@[simp]
theorem size_Roo {a b : Nat} :
    (a<...b).size = b - a - 1 := by
  simp [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[simp]
theorem size_Ric {b : Nat} :
    (*...=b).size = b + 1 := by
  simp [Ric.size, Rxc.HasSize.size]

@[simp]
theorem size_Rio {b : Nat} :
    (*...b).size = b := by
  simp [Rio.size, Rxo.HasSize.size, Rxc.HasSize.size]

end Std.PRange.Nat
