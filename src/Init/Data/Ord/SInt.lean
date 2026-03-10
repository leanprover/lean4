/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
public import Init.Data.Order.ClassesExtra
public import Init.Data.SInt.Basic
import Init.Data.SInt.Lemmas
import Init.Data.Order.Lemmas

public section

/-!
# Instances for fixed width signed integer types.

-/

set_option autoImplicit false
set_option linter.missingDocs true

open Std

namespace Int8

instance : Ord Int8 where
  compare x y := compareOfLT x y

instance : TransOrd Int8 := transCmp_compareOfLT

instance : LawfulEqOrd Int8 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd Int8 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end Int8

namespace Int16

instance : Ord Int16 where
  compare x y := compareOfLT x y

instance : TransOrd Int16 := transCmp_compareOfLT

instance : LawfulEqOrd Int16 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd Int16 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end Int16

namespace Int32

instance : Ord Int32 where
  compare x y := compareOfLT x y

instance : TransOrd Int32 := transCmp_compareOfLT

instance : LawfulEqOrd Int32 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd Int32 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end Int32

namespace Int64

instance : Ord Int64 where
  compare x y := compareOfLT x y

instance : TransOrd Int64 := transCmp_compareOfLT

instance : LawfulEqOrd Int64 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd Int64 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end Int64

namespace ISize

instance : Ord ISize where
  compare x y := compareOfLT x y

instance : TransOrd ISize := transCmp_compareOfLT

instance : LawfulEqOrd ISize where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd ISize where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end ISize
