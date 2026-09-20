/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
import Init.Data.Option.Lemmas
import Init.Omega

public section

namespace Std.PRange

instance : UpwardEnumerable Int where
  succ? x := some (x + 1)
  succMany? n x := some (x + n)

instance : LawfulUpwardEnumerable Int where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?, Option.some.injEq]
    omega
  succMany?_zero := by simp [UpwardEnumerable.succMany?]
  succMany?_add_one := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?,
      Option.bind_some, Option.some.injEq]
    omega

instance : InfinitelyUpwardEnumerable Int where
  isSome_succ? x := by simp [UpwardEnumerable.succ?]

instance : LawfulUpwardEnumerableLE Int where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, Int.le_def, Int.nonneg_def,
      Int.sub_eq_iff_eq_add', eq_comm (a := y)]

instance : LawfulUpwardEnumerableLT Int := inferInstance

instance : Rxc.HasSize Int where
  size lo hi := (hi + 1 - lo).toNat

instance : Rxc.LawfulHasSize Int where
  size_eq_zero_of_not_le lo hi := by
    simp only [Rxc.HasSize.size]
    omega
  size_eq_one_of_succ?_eq_none lo hi := by
    simp [Rxc.HasSize.size, UpwardEnumerable.succ?]

  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [UpwardEnumerable.succ?, Rxc.HasSize.size, Option.some.injEq]
    omega

instance : Rxc.IsAlwaysFinite Int := inferInstance

instance : Rxo.HasSize Int := .ofClosed
instance : Rxo.LawfulHasSize Int := inferInstance
instance : Rxo.IsAlwaysFinite Int := inferInstance

instance : DownwardEnumerable Int where
  pred? x := some (x - 1)
  predMany? n x := some (x - n)

instance : LawfulDownwardEnumerable Int where
  ne_of_lt := by
    simp only [DownwardEnumerable.LT, DownwardEnumerable.predMany?, Option.some.injEq]
    omega
  predMany?_zero := by simp [DownwardEnumerable.predMany?]
  predMany?_add_one := by
    simp only [DownwardEnumerable.predMany?, DownwardEnumerable.pred?, Option.bind_some,
      Option.some.injEq]
    omega

instance : InfinitelyDownwardEnumerable Int where
  isSome_pred? x := by simp [DownwardEnumerable.pred?]

instance : LawfulDownwardEnumerableLE Int where
  le_iff x y := by
    simp [DownwardEnumerable.LE, DownwardEnumerable.predMany?, Int.le_def, Int.nonneg_def,
      Int.sub_eq_iff_eq_add']
    constructor <;> rintro ⟨n, h⟩ <;> exists n <;> omega

instance : LawfulUpwardEnumerableLT Int := inferInstance

instance : Rcx.IsAlwaysFiniteRev Int where
  finite init lo := ⟨(init - lo).toNat + 1, by
    simp only [DownwardEnumerable.predMany?, Option.elim_some]
    omega⟩

instance : Rox.IsAlwaysFiniteRev Int where
  finite init lo := ⟨(init - lo).toNat + 1, by
    simp only [DownwardEnumerable.predMany?, Option.elim_some]
    omega⟩

end Std.PRange
