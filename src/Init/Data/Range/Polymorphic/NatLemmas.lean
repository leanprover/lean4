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

theorem toList_rco_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := by
  simp only [← succ_eq]
  rw [Std.Rco.toList_succ_succ_eq_map]

@[deprecated toList_rco_succ_succ (since := "2025-10-30")]
def toList_Rco_succ_succ := @toList_rco_succ_succ

@[deprecated toList_rco_succ_succ (since := "2025-08-22")]
def ClosedOpen.toList_succ_succ := @toList_rco_succ_succ

@[simp]
theorem size_rcc {a b : Nat} :
    (a...=b).size = b + 1 - a := by
  simp [Rcc.size, Rxc.HasSize.size]

@[deprecated size_rcc (since := "2025-10-30")]
def size_Rcc := @size_rcc

@[simp]
theorem size_rco {a b : Nat} :
    (a...b).size = b - a := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[deprecated size_rco (since := "2025-10-30")]
def size_Rco := @size_rco

@[simp]
theorem size_roc {a b : Nat} :
    (a<...=b).size = b - a := by
  simp [Roc.size, Rxc.HasSize.size]

@[deprecated size_roc (since := "2025-10-30")]
def size_Roc := @size_roc

@[simp]
theorem size_roo {a b : Nat} :
    (a<...b).size = b - a - 1 := by
  simp [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[deprecated size_roo (since := "2025-10-30")]
def size_Roo := @size_roo

@[simp]
theorem size_ric {b : Nat} :
    (*...=b).size = b + 1 := by
  simp [Ric.size, Rxc.HasSize.size]

@[deprecated size_ric (since := "2025-10-30")]
def size_Ric := @size_ric

@[simp]
theorem size_rio {b : Nat} :
    (*...b).size = b := by
  simp [Rio.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[deprecated size_rio (since := "2025-10-30")]
def size_Rio := @size_rio

end Std.PRange.Nat
