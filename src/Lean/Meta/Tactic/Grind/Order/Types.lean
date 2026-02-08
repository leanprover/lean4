/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public section
namespace Lean.Meta.Grind.Order

/-!
Solver for preorders, partial orders, linear orders, and support for offsets.
-/

abbrev NodeId := Nat

inductive CnstrKind where
  | le | lt
  deriving Inhabited

/--
A constraint of the form `u ≤ v + k` (`u < v + k` if `strict := true`)
Remark: If the order does not support offsets, then `k` is zero.
`h? := some h` if the Lean expression is not definitionally equal to the constraint,
but provably equal with proof `h`.
-/
structure Cnstr (α : Type) where
  kind   : CnstrKind
  u      : α
  v      : α
  k      : Int := 0
  /-- Denotation of this constraint as an expression. -/
  e      : Expr
  /--
  If `h? := some h`, then `h` is proof for that the expression associated with this constraint
  is equal to `e`. Recall that the input constraints are normalized. For example, given `x y : Int`,
  `x ≤ y` is internally represented as `x ≤ y + 0`
  -/
  h?     : Option Expr := none
  deriving Inhabited

structure Weight where
  k : Int := 0
  strict := false
  deriving Inhabited

/-- Auxiliary structure used for proof extraction.  -/
structure ProofInfo where
  w      : NodeId
  k      : Weight
  proof  : Expr
  deriving Inhabited

/--
Auxiliary inductive type for representing constraints and equalities
that should be propagated to core.
Recall that we cannot compute proofs until the short-distance
data-structures have been fully updated when a new edge is inserted.
Thus, we store the information to be propagated into a list.
See field `propagate` in `State`.
-/
inductive ToPropagate where
  | eqTrue (c : Cnstr NodeId) (e : Expr) (u v : NodeId) (k k' : Weight)
  | eqFalse (c : Cnstr NodeId) (e : Expr) (u v : NodeId) (k k' : Weight)
  | eq (u v : NodeId)
  deriving Inhabited

/--
State for each order structure processed by this module.
Each type must at least implement the instance `Std.IsPreorder`.
-/
structure Struct where
  id                 : Nat
  type               : Expr
  /-- Cached `getDecLevel type` -/
  u                  : Level
  isPreorderInst     : Expr
  /-- `LE` instance  -/
  leInst             : Expr
  /-- `LT` instance if available -/
  ltInst?            : Option Expr
  /-- `IsPartialOrder` instance if available -/
  isPartialInst?     : Option Expr
  /-- `IsLinearPreorder` instance if available -/
  isLinearPreInst?   : Option Expr
  /-- `LawfulOrderLT` instance if available -/
  lawfulOrderLTInst? : Option Expr
  /-- `id` of the `CommRing` (or `Ring`) structure in the `grind ring` module if available. -/
  ringId?            : Option Nat
  /-- `true` if `ringId?` is the Id of a commutative ring -/
  isCommRing         : Bool
  /-- `Ring` instance if available -/
  ringInst?          : Option Expr
  /-- `OrderedRing` instance if available -/
  orderedRingInst?   : Option Expr
  leFn               : Expr
  ltFn?              : Option Expr
  /-- Mapping from `NodeId` to the `Expr` represented by the node. -/
  nodes              : PArray Expr := {}
  /-- Mapping from `Expr` to a node representing it. -/
  nodeMap            : PHashMap ExprPtr NodeId := {}
  /-- Mapping from `Expr` representing inequalities to constraints. -/
  cnstrs             : PHashMap ExprPtr (Cnstr NodeId) := {}
  /--
  Mapping from pairs `(u, v)` to a list of constraints on `u` and `v`.
  We use this mapping to implement exhaustive constraint propagation.
  -/
  cnstrsOf           : PHashMap (NodeId × NodeId) (List (Cnstr NodeId × Expr)) := {}
  /--
  For each node with id `u`, `sources[u]` contains
  pairs `(v, k)` s.t. there is a path from `v` to `u` with weight `k`.
  -/
  sources            : PArray (AssocList NodeId Weight) := {}
  /--
  For each node with id `u`, `targets[u]` contains
  pairs `(v, k)` s.t. there is a path from `u` to `v` with weight `k`.
  -/
  targets            : PArray (AssocList NodeId Weight) := {}
  /--
  Proof reconstruction information. For each node with id `u`, `proofs[u]` contains
  pairs `(v, { w, proof })` s.t. there is a path from `u` to `v`, and
  `w` is the penultimate node in the path, and `proof` is the justification for
  the last edge.
  -/
  proofs             : PArray (AssocList NodeId ProofInfo) := {}
  /-- Truth values and equalities to propagate to core. -/
  propagate          : List ToPropagate := []
  deriving Inhabited

/-- State for all order types detected by `grind`. -/
structure State where
  /-- Order structures detected. -/
  structs : Array Struct := {}
  /--
  Mapping from types to its "structure id". We cache failures using `none`.
  `typeIdOf[type]` is `some id`, then `id < structs.size`. -/
  typeIdOf : PHashMap ExprPtr (Option Nat) := {}
  /-- Mapping from expressions/terms to their structure ids. -/
  exprToStructId : PHashMap ExprPtr Nat := {}
  /--
  Mapping from terms/constraints that have been mapped into `Ring`s before being internalized.
  Example: given `x y : Nat`, `x ≤ y + 1` is mapped to `Int.ofNat x ≤ Int.ofNat y + 1`, and proof
  of equivalence.
  -/
  termMap    : PHashMap ExprPtr (Expr × Expr) := {}
  /-- `termMap` inverse -/
  termMapInv : PHashMap ExprPtr (Expr × Expr) := {}
  deriving Inhabited

builtin_initialize orderExt : SolverExtension State ← registerSolverExtension (return {})

def get' : GoalM State := do
  orderExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  orderExt.modifyState f

end Lean.Meta.Grind.Order
