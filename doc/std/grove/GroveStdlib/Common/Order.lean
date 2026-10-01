/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/

open Std

namespace GroveStdlib.Common

namespace OrderClasses

public def orderDataClasses : Array Lean.Name :=
  #[``BEq, ``LE, ``LT, ``Ord, ``Min, ``Max]

public def decidableOrderClasses : Array Lean.Name :=
  #[``DecidableEq, ``DecidableLE, ``DecidableLT]

public def orderLawClasses : Array Lean.Name :=
  #[``IsPreorder, ``Std.IsPartialOrder, ``Std.IsLinearPreorder, ``Std.IsLinearOrder]

public def orderCompatibilityClasses : Array Lean.Name :=
  #[``LawfulOrderLT, ``LawfulOrderBEq, ``LawfulOrderOrd]

public def minMaxClasses : Array Lean.Name :=
  #[``LawfulOrderMin, ``LawfulOrderInf, ``LawfulOrderLeftLeaningMin, ``LawfulOrderMax, ``LawfulOrderSup, ``LawfulOrderLeftLeaningMax]

public def ordClasses : Array Lean.Name :=
  #[``ReflOrd, ``OrientedOrd, ``TransOrd, ``LawfulEqOrd, ``LawfulBEqOrd]

public def beqClasses : Array Lean.Name :=
  #[``EquivBEq, ``LawfulBEq]

public def orderClasses : Array Lean.Name :=
  orderDataClasses ++ decidableOrderClasses ++ orderLawClasses ++ orderCompatibilityClasses ++ minMaxClasses ++ ordClasses ++ beqClasses

end OrderClasses

end GroveStdlib.Common
