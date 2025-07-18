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

def associativeContainers : List Lean.Name :=
  [`Std.DHashMap, `Std.DHashMap.Raw, `Std.ExtDHashMap, `Std.DTreeMap, `Std.DTreeMap.Raw, `Std.ExtDTreeMap, `Std.HashMap,
   `Std.HashMap.Raw, `Std.ExtHashMap, `Std.TreeMap, `Std.TreeMap.Raw, `Std.ExtTreeMap, `Std.HashSet, `Std.HashSet.Raw, `Std.ExtHashSet,
   `Std.TreeSet, `Std.TreeSet.Raw, `Std.ExtTreeSet]

def associativeQueryOperations : AssociationTable .subexpression associativeContainers where
  id := "associative-query-operations"
  title := "Associative query operations"
  description := "Operations that take as input an associative container and return a 'single' piece of information (e.g., `GetElem` or `isEmpty`, but not `toList`)."
  dataSources n :=
    (DataSource.definitionsInNamespace n)
      |>.map Subexpression.declaration
      |>.or (DataSource.getElem n)

def associativeCreationOperations : AssociationTable .subexpression associativeContainers where
  id := "associative-creation-operations"
  title := "Associative creation operations"
  description := "Operations that create a new associative container"
  dataSources n :=
    (DataSource.definitionsInNamespace n)
      |>.map Subexpression.declaration
      |>.or (DataSource.emptyCollection n)

def associativeModificationOperations : AssociationTable .subexpression associativeContainers where
  id := "associative-modification-operations"
  title := "Associative modification operations"
  description := "Operations that both accept and return an associative container"
  dataSources n :=
    (DataSource.definitionsInNamespace n)
      |>.map Subexpression.declaration

def associativeCreateThenQuery : Table .subexpression .subexpression .declaration associativeContainers where
  id := "associative-create-then-query"
  title := "Associative create then query"
  description := "Lemmas that say what happens when creating a new associative container and then immediately querying from it"
  rowsFrom := .table associativeCreationOperations
  columnsFrom := .table associativeQueryOperations
  cellData := .classic _ { relevantNamespaces := associativeContainers }

def allOperationsCovered : Assertion where
  widgetId := "associative-all-operations-covered"
  title := "All operations on associative containers covered"
  description := "All operations on an associative container should appear in at least one of the tables"
  check := do
    let allValuesArray : Array String ← #[associativeQueryOperations, associativeCreationOperations, associativeModificationOperations].flatMapM valuesInAssociationTable
    let allValues : Std.HashSet String := Std.HashSet.ofArray allValuesArray
    let env ← Lean.getEnv
    let mut numBad := 0
    for (n, _) in env.constants do
      if associativeContainers.any (fun namesp => namesp.isPrefixOf n) then
        if !n.toString ∈ allValues then
          numBad := numBad + 1
    return #[{
      assertionId := "all-covered"
      description := "All operations should be covered"
      passed := numBad == 0
      message := if numBad = 0 then "All operations were covered" else s!"There were {numBad} operations that were not covered."
    }]

end AssociativeContainers

open AssociativeContainers in
def associativeContainers : Node :=
  .section "associative-containers" "Associative containers" #[
    .associationTable associativeQueryOperations,
    .associationTable associativeCreationOperations,
    .associationTable associativeModificationOperations,
    .table associativeCreateThenQuery,
    .assertion allOperationsCovered
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
