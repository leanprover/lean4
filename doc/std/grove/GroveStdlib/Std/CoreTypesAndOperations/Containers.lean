/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework

open Grove.Framework Widget

namespace GroveStdlib.Std.CoreTypesAndOperations

namespace Containers

namespace SequentialContainers

end SequentialContainers

def sequentialContainers : Node :=
  .section "sequential-containers" "Sequential containers" #[]

namespace AssociativeContainers

def associativeQueryOperations : AssociationTable .subexpression
    [`Std.DHashMap, `Std.DHashMap.Raw, `Std.ExtDHashMap, `Std.DTreeMap, `Std.DTreeMap.Raw, `Std.ExtDTreeMap, `Std.HashMap,
     `Std.HashMap.Raw, `Std.ExtHashMap, `Std.TreeMap, `Std.TreeMap.Raw, `Std.ExtTreeMap, `Std.HashSet, `Std.HashSet.Raw, `Std.ExtHashSet,
     `Std.TreeSet, `Std.TreeSet.Raw, `Std.ExtTreeSet] where
  id := "associative-query-operations"
  title := "Associative query operations"
  description := "Operations that take as input an associative container and return a 'single' piece of information (e.g., `GetElem` or `isEmpty`, but not `toList`)."
  dataSources n :=
    (DataSource.declarationsInNamespace n .definitionsOnly)
      |>.map Subexpression.declaration
      |>.or (DataSource.getElem n)

end AssociativeContainers

def associativeContainers : Node :=
  .section "associative-containers" "Associative containers" #[
    .associationTable AssociativeContainers.associativeQueryOperations
  ]

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
