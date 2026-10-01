/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework
import GroveStdlib.Common.Order

open Grove.Framework Widget
open Std
open GroveStdlib.Common

namespace GroveStdlib.Std.CoreTypesAndOperations

namespace Numbers

def unboundedNumericTypes : Array Lean.Name := #[``Nat, ``Int]
def boundedNumericTypes : Array Lean.Name := #[
  ``Fin, ``BitVec,
  ``Int8, ``Int16, ``Int32, ``Int64, ``ISize,
  ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize
]
def float : Array Lean.Name := #[``Float]

def numericTypes : Array Lean.Name :=
  unboundedNumericTypes ++ boundedNumericTypes ++ float

def orderInstances : Table .declaration .declaration .synthesis [()] where
  id := "numeric-order-instances"
  title := "Order instances on numeric types"
  rowsFrom := .constUnit (pure numericTypes)
  columnsFrom := .constUnit (pure OrderClasses.orderClasses)
  cellData := .synthesis #[]

end Numbers

def numbers : Node :=
  .section "numbers" "Numbers" #[.table Numbers.orderInstances]

end GroveStdlib.Std.CoreTypesAndOperations
