/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
import Grove.Framework
import GroveStdlib.Common.Order

open Grove.Framework Widget
open GroveStdlib.Common

namespace GroveStdlib.Std.CoreTypesAndOperations

namespace Containers

namespace SequentialContainers

def sequentialContainerTypes : Array Lean.Name := #[
  ``List, ``Array, ``Vector, ``ByteArray, ``FloatArray
]

def orderInstances : Table .declaration .declaration .synthesis [()] where
  id := "sequential-container-order-instances"
  title := "Order instances on sequantial containers"
  rowsFrom := .constUnit (pure sequentialContainerTypes)
  columnsFrom := .constUnit (pure OrderClasses.orderClasses)
  cellData := .synthesis OrderClasses.orderClasses

end SequentialContainers

open SequentialContainers

def sequentialContainers : Node :=
  .section "sequential-containers" "Sequential containers" #[
    .table orderInstances
  ]

end Containers

end GroveStdlib.Std.CoreTypesAndOperations
