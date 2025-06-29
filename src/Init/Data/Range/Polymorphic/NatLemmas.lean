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

theorem succ_eq {n : Nat} : UpwardEnumerable.succ n = n + 1 :=
  rfl

theorem ClosedOpen.toList_succ_succ  {m n : Nat} :
    (PRange.mk (shape := ⟨.closed, .open⟩) (m+1) (n+1)).toList =
      (PRange.mk (shape := ⟨.closed, .open⟩) m n).toList.map (· + 1) := by
  simp only [← succ_eq]
  rw [Std.PRange.ClosedOpen.toList_succ_succ_eq_map]

end Std.PRange.Nat
