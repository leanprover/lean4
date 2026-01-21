/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Fin.OverflowAware
import Init.Grind

public section

open Std Std.PRange

namespace Fin

instance : UpwardEnumerable (Fin n) where
  succ? i := i.addNat? 1
  succMany? m i := i.addNat? m

@[simp]
theorem pRangeSucc?_eq : PRange.succ? (α := Fin n) = (·.addNat? 1) := rfl

@[simp]
theorem pRangeSuccMany?_eq : PRange.succMany? m (α := Fin n) = (·.addNat? m) :=
  rfl

instance : LawfulUpwardEnumerable (Fin n) where
  ne_of_lt a b := by
    simpa [UpwardEnumerable.LT, ← Fin.val_inj, Fin.addNat?_eq_some_iff] using by grind
  succMany?_zero a := by simp
  succMany?_add_one m a := by simpa [Fin.addNat?_eq_dif] using by grind

instance : LawfulUpwardEnumerableLE (Fin n) where
  le_iff x y := by
    simp only [le_def, UpwardEnumerable.LE, pRangeSuccMany?_eq, Fin.addNat?_eq_dif,
      Option.dite_none_right_eq_some, Option.some.injEq, ← val_inj, exists_prop]
    exact ⟨fun h => ⟨y - x, by grind⟩, by grind⟩

instance : Least? (Fin 0) where
  least? := none

instance : LawfulUpwardEnumerableLeast? (Fin 0) where
  least?_le a := False.elim (Nat.not_lt_zero _ a.isLt)

@[simp]
theorem least?_eq_of_zero : Least?.least? (α := Fin 0) = none := rfl

instance [NeZero n] : Least? (Fin n) where
  least? := some 0

instance [NeZero n] : LawfulUpwardEnumerableLeast? (Fin n) where
  least?_le a := ⟨0, rfl, (LawfulUpwardEnumerableLE.le_iff 0 a).1 (Fin.zero_le _)⟩

@[simp]
theorem least?_eq [NeZero n] : Least?.least? (α := Fin n) = some 0 := rfl

instance : LawfulUpwardEnumerableLT (Fin n) := inferInstance

instance : Rxc.HasSize (Fin n) where
  size lo hi := hi + 1 - lo

instance : Rxc.LawfulHasSize (Fin n) where
  size_eq_zero_of_not_le bound x := by
    simp [Rxc.HasSize.size, Fin.lt_def]
    grind
  size_eq_one_of_succ?_eq_none lo hi := by
    simp [Rxc.HasSize.size, Fin.le_def, UpwardEnumerable.succ?]
    grind
  size_eq_succ_of_succ?_eq_some lo hi x := by
    simp [Rxc.HasSize.size, Fin.le_def, UpwardEnumerable.succ?]
    grind [Fin.addNat?_eq_dif]

instance : Rxc.IsAlwaysFinite (Fin n) := inferInstance

instance : Rxo.HasSize (Fin n) := .ofClosed
instance : Rxo.LawfulHasSize (Fin n) := inferInstance
instance : Rxo.IsAlwaysFinite (Fin n) := inferInstance

instance : Rxi.HasSize (Fin n) where
  size lo := n - lo

instance : Rxi.LawfulHasSize (Fin n) where
  size_eq_one_of_succ?_eq_none x := by
    simp [Rxi.HasSize.size, UpwardEnumerable.succ?]
    grind
  size_eq_succ_of_succ?_eq_some lo lo' := by
    simp [Rxi.HasSize.size, UpwardEnumerable.succ?]
    grind [Fin.addNat?_eq_dif]

instance : Rxi.IsAlwaysFinite (Fin n) := inferInstance

end Fin
