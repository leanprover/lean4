/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas

set_option doc.verso true

public section

namespace Fin

/--
Overflow-aware addition of a natural number to an element of {lean}`Fin n`.

Examples:
* {lean}`(2 : Fin 3).addNat? 1 = (none : Option (Fin 3))`
* {lean}`(2 : Fin 4).addNat? 1 = (some 3 : Option (Fin 4))`
-/
@[inline]
protected def addNat? (i : Fin n) (m : Nat) : Option (Fin n) :=
  if h : i + m < n then some ⟨i + m, h⟩ else none

theorem addNat?_eq_some {i : Fin n} (h : i + m < n) : i.addNat? m = some ⟨i + m, h⟩ := by
  simp [Fin.addNat?, h]

theorem addNat?_eq_some_iff {i : Fin n} :
    i.addNat? m = some j ↔ i + m < n ∧ j = i + m := by
  simp only [Fin.addNat?]
  split <;> simp [Fin.ext_iff, eq_comm, *]

@[simp]
theorem addNat?_eq_none_iff {i : Fin n} : i.addNat? m = none ↔ n ≤ i + m := by
  simp only [Fin.addNat?]
  split <;> simp_all [Nat.not_lt]

@[simp]
theorem addNat?_zero {i : Fin n} : i.addNat? 0 = some i := by
  simp [addNat?_eq_some_iff]

@[grind =]
theorem addNat?_eq_dif {i : Fin n} :
    i.addNat? m = if h : i + m < n then some ⟨i + m, h⟩ else none := by
  rfl

end Fin
