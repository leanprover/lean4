/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework

open Grove.Framework Widget
open Std

namespace GroveStdlib.Std.CoreTypesAndOperations

namespace Numbers

def unboundedNumericTypes : Array Lean.Name := #[``Nat, ``Int]
def boundedNumericTypes : Array Lean.Name := #[
  ``Fin,
  ``Int8, ``Int16, ``Int32, ``Int64, ``ISize,
  ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize
]
def float : Array Lean.Name := #[``Float]

def numericTypes : Array Lean.Name :=
  unboundedNumericTypes ++ boundedNumericTypes ++ float

def orderDataClasses : Array Lean.Name :=
  #[``BEq, ``LE, ``LT, ``Ord, ``Min, ``Max]

def decidableOrderClasses : Array Lean.Name :=
  #[``DecidableEq, ``DecidableLE, ``DecidableLT]

def orderLawClasses : Array Lean.Name :=
  #[``IsPreorder, ``Std.IsPartialOrder, ``Std.IsLinearPreorder, ``Std.IsLinearOrder]

def orderCompatibilityClasses : Array Lean.Name :=
  #[``LawfulOrderLT, ``LawfulOrderBEq, ``LawfulOrderOrd]

def minMaxClasses : Array Lean.Name :=
  #[``LawfulOrderMin, ``LawfulOrderInf, ``LawfulOrderLeftLeaningMin, ``LawfulOrderMax, ``LawfulOrderSup, ``LawfulOrderLeftLeaningMax]

def ordClasses : Array Lean.Name :=
  #[``ReflOrd, ``OrientedOrd, ``TransOrd, ``LawfulEqOrd, ``LawfulBEqOrd]

def beqClasses : Array Lean.Name :=
  #[``EquivBEq, ``LawfulBEq]

def orderClasses : Array Lean.Name :=
  orderDataClasses ++ decidableOrderClasses ++ orderLawClasses ++ orderCompatibilityClasses ++ minMaxClasses ++ ordClasses ++ beqClasses

def orderInstances : Table .declaration .declaration .synthesis [()] where
  id := "numeric-order-instances"
  title := "Order instances on numeric types"
  rowsFrom := .constUnit (pure numericTypes)
  columnsFrom := .constUnit (pure orderClasses)
  cellData := .synthesis #[]

end Numbers

def numbers : Node :=
  .section "numbers" "Numbers" #[.table Numbers.orderInstances]

end GroveStdlib.Std.CoreTypesAndOperations
