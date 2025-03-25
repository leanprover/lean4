/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Std.Data.TreeSet.Basic
import Std.Data.TreeSet.Lemmas
import Std.Data.HashMap

open Std

variable {α : Type u} {β : Type v} [Ord α]

def mkDTreeMapSingleton (a : α) (b : β) : DTreeMap α (fun _ => β) := Id.run do
  let mut m : DTreeMap α (fun _ => β) := ∅
  m := m.insert a b
  return m

def mkTreeMapSingleton (a : α) (b : β) : TreeMap α β := Id.run do
  let mut m : TreeMap α β := ∅
  m := m.insert a b
  return m

def mkTreeSetSingleton (a : α) : TreeSet α := Id.run do
  let mut m : TreeSet α := ∅
  m := m.insert a
  return m

example [TransOrd α] [LawfulEqOrd α] (a : α) (b : β) : Option β :=
  mkDTreeMapSingleton a b |>.get? a

example [TransOrd α] [LawfulEqOrd α] (a : α) (b : β) : Option β :=
  (mkTreeMapSingleton a b)[a]?

example [TransOrd α] (a : α) (b : β) : (mkTreeMapSingleton a b).contains a := by
  simp [mkTreeMapSingleton, Id.run]

example [TransOrd α] (a : α) (b : β) : (mkDTreeMapSingleton a b).contains a := by
  simp [mkDTreeMapSingleton, Id.run]

example [TransOrd α] (a : α) : (mkTreeSetSingleton a).contains a := by
  simp [mkTreeSetSingleton, Id.run]

section Dijkstra

variable {α : Type u} [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]

variable (α) in
abbrev PriorityQueueKey := Nat × α

local instance : Ord (PriorityQueueKey α) := lexOrd

variable (α) in
structure NodeState where
  currentPathAndDistanceToTarget : Option (List α × Nat)
  done : Bool

variable (α) in
structure DijkstraState where
  weightedEdges : TreeMap α (List (α × Nat))
  source : α
  target : α
  nodeStates : TreeMap α (NodeState α)
  priorityQueue : TreeSet (PriorityQueueKey α)
  source_mem : source ∈ weightedEdges
  target_mem : target ∈ weightedEdges
  closed : ∀ a, (ha : a ∈ weightedEdges) → ∀ p ∈ weightedEdges.get a ha, p.1 ∈ weightedEdges


variable (α) in
def DijkstraState := { state : DijkstraStateRaw α //
    (∀ a : α, a ∈ state.weightedEdges ↔ a ∈ state.nodeStates) }

def DijkstraState.done (state : DijkstraState α) : Bool :=
  state.nodeStates.get? state.source

def iterateDijkstra (state : DijkstraState α)

def shortestPath (weightedEdges : α → α × Nat) (source target : α) : List α := Id.run do
  let mut priorityQueue : TreeMap

end Dijkstra
