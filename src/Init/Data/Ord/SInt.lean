/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
public import Init.Data.SInt.Basic
import Init.Data.SInt.Lemmas

public section

/-!
# Instances for fixed width signed integer types.

-/

set_option autoImplicit false
set_option linter.missingDocs true

open Std

namespace Int8

instance : Ord Int8 where
  compare x y := compareOfLessAndEq x y

instance : TransOrd Int8 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int8.le_antisymm Int8.le_trans Int8.le_total Int8.not_le

instance : LawfulEqOrd Int8 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int8.le_refl Int8.not_le |>.mp h

end Int8

namespace Int16

instance : Ord Int16 where
  compare x y := compareOfLessAndEq x y

instance : TransOrd Int16 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int16.le_antisymm Int16.le_trans Int16.le_total Int16.not_le

instance : LawfulEqOrd Int16 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int16.le_refl Int16.not_le |>.mp h

end Int16

namespace Int32

instance : Ord Int32 where
  compare x y := compareOfLessAndEq x y

instance : TransOrd Int32 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int32.le_antisymm Int32.le_trans Int32.le_total Int32.not_le

instance : LawfulEqOrd Int32 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int32.le_refl Int32.not_le |>.mp h

end Int32

namespace Int64

instance : Ord Int64 where
  compare x y := compareOfLessAndEq x y

instance : TransOrd Int64 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Int64.le_antisymm Int64.le_trans Int64.le_total Int64.not_le

instance : LawfulEqOrd Int64 where
  eq_of_compare h := compareOfLessAndEq_eq_eq Int64.le_refl Int64.not_le |>.mp h

end Int64

namespace ISize

instance : Ord ISize where
  compare x y := compareOfLessAndEq x y

instance : TransOrd ISize :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    ISize.le_antisymm ISize.le_trans ISize.le_total ISize.not_le

instance : LawfulEqOrd ISize where
  eq_of_compare h := compareOfLessAndEq_eq_eq ISize.le_refl ISize.not_le |>.mp h

end ISize
