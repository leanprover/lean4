/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.Offset.Util

namespace Lean.Meta.Grind.Arith.Offset

abbrev NodeId := Nat

instance : ToMessageData (Offset.Cnstr NodeId) where
  toMessageData c := Offset.toMessageData (α := NodeId) (inst := { toMessageData n := m!"#{n}" }) c

/-- Auxiliary structure used for proof extraction.  -/
structure ProofInfo where
  w     : NodeId
  k     : Int
  proof : Expr
  deriving Inhabited

/--
Auxiliary inductive type for representing contraints and equalities
that should be propagated to core.
Recall that we cannot compute proofs until the short-distance
data-structures have been fully updated when a new edge is inserted.
Thus, we store the information to be propagated into a list.
See field `propagate` in `State`.
-/
inductive ToPropagate where
  | eqTrue (e : Expr) (u v : NodeId) (k k' : Int)
  | eqFalse (e : Expr) (u v : NodeId) (k k' : Int)
  | eq (u v : NodeId)
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
  proofs    : PArray (AssocList NodeId ProofInfo) := {}
  /-- Truth values and equalities to propagate to core. -/
  propagate : List ToPropagate := []
  deriving Inhabited

end Lean.Meta.Grind.Arith.Offset
