/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util

namespace Lean.Meta.Grind.Arith

namespace Offset

abbrev NodeId := Nat

instance : ToMessageData (Offset.Cnstr NodeId) where
  toMessageData c := Offset.toMessageData (α := NodeId) (inst := { toMessageData n := m!"#{n}" }) c

/-- Auxiliary structure used for proof extraction.  -/
structure ProofInfo where
  w     : NodeId
  k     : Int
  proof : Expr
  deriving Inhabited

/-- State of the constraint offset procedure. -/
structure State where
  /-- Mapping from `NodeId` to the `Expr` represented by the node. -/
  nodes    : PArray Expr := {}
  /-- Mapping from `Expr` to a node representing it. -/
  nodeMap  : PHashMap ENodeKey NodeId := {}
  /-- Mapping from `Expr` representing inequalites to constraints. -/
  cnstrs   : PHashMap ENodeKey (Cnstr NodeId) := {}
  /--
  Mapping from pairs `(u, v)` to a list of offset constraints on `u` and `v`.
  We use this mapping to implement exhaustive constraint propagation.
  -/
  cnstrsOf : PHashMap (NodeId × NodeId) (List (Cnstr NodeId × Expr)) := {}
  /--
  For each node with id `u`, `sources[u]` contains
  pairs `(v, k)` s.t. there is a path from `v` to `u` with weight `k`.
  -/
  sources  : PArray (AssocList NodeId Int) := {}
  /--
  For each node with id `u`, `targets[u]` contains
  pairs `(v, k)` s.t. there is a path from `u` to `v` with weight `k`.
  -/
  targets  : PArray (AssocList NodeId Int) := {}
  /--
  Proof reconstruction information. For each node with id `u`, `proofs[u]` contains
  pairs `(v, { w, proof })` s.t. there is a path from `u` to `v`, and
  `w` is the penultimate node in the path, and `proof` is the justification for
  the last edge.
  -/
  proofs   : PArray (AssocList NodeId ProofInfo) := {}
  deriving Inhabited

end Offset

/-- State for the arithmetic procedures. -/
structure State where
  offset : Offset.State := {}
  deriving Inhabited

end Lean.Meta.Grind.Arith
