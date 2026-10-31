/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework
import GroveStdlib.Std.CoreTypesAndOperations.Containers.AssociativeContainers
import GroveStdlib.Std.CoreTypesAndOperations.Containers.SequentialContainers

open Grove.Framework Widget

namespace GroveStdlib.Std.CoreTypesAndOperations

namespace Containers

namespace PersistentDataStructures

end PersistentDataStructures

def persistentDataStructures : Node :=
  .section "persistent-data-structures" "Persistent data structures" #[]

end Containers

def containers : Node :=
  .section "containers" "Containers" #[
    Containers.sequentialContainers,
    Containers.associativeContainers,
    Containers.persistentDataStructures
  ]

end GroveStdlib.Std.CoreTypesAndOperations
