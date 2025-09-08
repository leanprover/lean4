/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Classes
public import Init.Data.Int.Order
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
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?,
      Option.bind_some, Option.some.injEq]
    omega

instance : InfinitelyUpwardEnumerable Int where
  isSome_succ? x := by simp [UpwardEnumerable.succ?]

instance : LawfulUpwardEnumerableLE Int where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, Int.le_def, Int.nonneg_def,
      Int.sub_eq_iff_eq_add', eq_comm (a := y)]

instance : LawfulOrderLT Int := inferInstance
instance : LawfulUpwardEnumerableLT Int := inferInstance
instance : LawfulUpwardEnumerableLT Int := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed Int := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed Int := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open Int := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open Int := inferInstance

instance : RangeSize .closed Int where
  size bound a := (bound + 1 - a).toNat

instance : RangeSize .open Int := RangeSize.openOfClosed

instance : LawfulRangeSize .closed Int where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp only [SupportsUpperBound.IsSatisfied, RangeSize.size]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp [SupportsUpperBound.IsSatisfied, RangeSize.size, UpwardEnumerable.succ?]

  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, UpwardEnumerable.succ?, RangeSize.size,
      Option.some.injEq]
    omega

end Std.PRange
