/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
import Init.Grind

public section

open Std Std.PRange

namespace Fin

instance : UpwardEnumerable (Fin n) where
  succ? i := if h : i + 1 < n then some ⟨i + 1, h⟩ else none
  succMany? i m := if h : i + m < n then some ⟨i + m, h⟩ else none

instance : LawfulUpwardEnumerable (Fin n) where
  ne_of_lt a b := by
    simpa [UpwardEnumerable.LT, UpwardEnumerable.succMany?, ← Fin.val_inj] using by grind
  succMany?_zero a := by simp [UpwardEnumerable.succMany?]
  succMany?_add_one n a := by
    simpa [UpwardEnumerable.succMany?, UpwardEnumerable.succ?] using by grind

instance : LawfulUpwardEnumerableLE (Fin n) where
  le_iff x y := by
    simp only [le_def, UpwardEnumerable.LE, succMany?, Option.dite_none_right_eq_some,
      Option.some.injEq, ← val_inj, exists_prop]
    exact ⟨fun h => ⟨y - x, by grind⟩, by grind⟩

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
    grind

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
    grind

instance : Rxi.IsAlwaysFinite (Fin n) := inferInstance

end Fin
