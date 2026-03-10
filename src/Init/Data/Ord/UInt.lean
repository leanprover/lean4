/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
public import Init.Data.Order.ClassesExtra
public import Init.Data.UInt.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Order.Lemmas

public section

/-!
# Instances for fixed width unsigned integer types.

-/

set_option autoImplicit false
set_option linter.missingDocs true

open Std

namespace UInt8

instance : Ord UInt8 where
  compare x y := compareOfLT x y

instance : TransOrd UInt8 := transCmp_compareOfLT

instance : LawfulEqOrd UInt8 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd UInt8 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end UInt8

namespace UInt16

instance : Ord UInt16 where
  compare x y := compareOfLT x y

instance : TransOrd UInt16 := transCmp_compareOfLT

instance : LawfulEqOrd UInt16 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd UInt16 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end UInt16

namespace UInt32

instance : Ord UInt32 where
  compare x y := compareOfLT x y

instance : TransOrd UInt32 := transCmp_compareOfLT

instance : LawfulEqOrd UInt32 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd UInt32 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end UInt32

namespace UInt64

instance : Ord UInt64 where
  compare x y := compareOfLT x y

instance : TransOrd UInt64 := transCmp_compareOfLT

instance : LawfulEqOrd UInt64 where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd UInt64 where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end UInt64

namespace USize

instance : Ord USize where
  compare x y := compareOfLT x y

instance : TransOrd USize := transCmp_compareOfLT

instance : LawfulEqOrd USize where
  eq_of_compare h := (compareOfLT_eq_eq).mp h

instance : LawfulOrderOrd USize where
  isLE_compare _ _ := isLE_compareOfLT
  isGE_compare _ _ := isGE_compareOfLT

end USize
