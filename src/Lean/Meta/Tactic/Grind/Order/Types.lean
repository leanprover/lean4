/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Init.Data.Rat.Basic
public section
namespace Lean.Meta.Grind.Order

/-!
Solver for preorders, partial orders, linear orders, and support for offsets.
-/

abbrev NodeId := Nat
/--
**Note**: We use `Int` to represent weights, but solver supports `Unit` (encoded as `0`),
`Nat`, and `Int`. During proof construction we perform the necessary conversions.
-/
abbrev Weight := Int

/--
A constraint of the form `u + k₁ ≤ v + k₂` (`u + k₁ < v + k₂` if `strict := true`)
Remark: If the order does not support offsets, then `k₁` and `k₂` are zero.
`h? := some h` if the Lean expression is not definitionally equal to the constraint,
but provably equal with proof `h`.
-/
structure Cnstr where
  u      : NodeId
  v      : NodeId
  strict : Bool   := false
  k₁     : Weight := 0
  k₂     : Weight := 0
  h?     : Option Expr := none
  deriving Inhabited

structure WeightS where
  w : Rat
  strict := false

def WeightS.compare (a b : WeightS) : Ordering :=
  if a.w < b.w then
    .lt
  else if b.w > a.w then
    .gt
  else if a.strict == b.strict then
    .eq
  else if !a.strict && b.strict then
    .lt
  else
    .gt

instance : Ord WeightS where
  compare := WeightS.compare

instance : LE WeightS where
  le a b := compare a b ≠ .gt

instance : LT WeightS where
  lt a b := compare a b = .lt

instance : DecidableLE WeightS :=
  fun a b => inferInstanceAs (Decidable (compare a b ≠ .gt))

instance : DecidableLT WeightS :=
  fun a b => inferInstanceAs (Decidable (compare a b = .lt))

/-- Auxiliary structure used for proof extraction.  -/
structure ProofInfo where
  w      : NodeId
  strict : Bool := false
  k₁     : Rat := 0
  k₂     : Rat := 0
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
  | eqTrue (e : Expr) (u v : NodeId) (k k' : Int)
  | eqFalse (e : Expr) (u v : NodeId) (k k' : Int)
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
  leFn               : Expr
  ltFn?              : Option Expr
  -- TODO: offset instances
  /-- Mapping from `NodeId` to the `Expr` represented by the node. -/
  nodes              : PArray Expr := {}
  /-- Mapping from `Expr` to a node representing it. -/
  nodeMap            : PHashMap ExprPtr NodeId := {}
  /-- Mapping from `Expr` representing inequalities to constraints. -/
  cnstrs             : PHashMap ExprPtr Cnstr := {}
  /--
  Mapping from pairs `(u, v)` to a list of constraints on `u` and `v`.
  We use this mapping to implement exhaustive constraint propagation.
  -/
  cnstrsOf           : PHashMap (NodeId × NodeId) (List (NodeId × Expr)) := {}
  /--
  For each node with id `u`, `sources[u]` contains
  pairs `(v, k)` s.t. there is a path from `v` to `u` with weight `k`.
  -/
  sources            : PArray (AssocList NodeId WeightS) := {}
  /--
  For each node with id `u`, `targets[u]` contains
  pairs `(v, k)` s.t. there is a path from `u` to `v` with weight `k`.
  -/
  targets            : PArray (AssocList NodeId WeightS) := {}
  /--
  Proof reconstruction information. For each node with id `u`, `proofs[u]` contains
  pairs `(v, { w, proof })` s.t. there is a path from `u` to `v`, and
  `w` is the penultimate node in the path, and `proof` is the justification for
  the last edge.
  -/
  proofs             : PArray (AssocList NodeId ProofInfo) := {}
  /-- Truth values and equalities to propagate to core. -/
  propagate : List ToPropagate := []
  deriving Inhabited

/-- State for all order types detected by `grind`. -/
structure State where
  /-- Order structures detected. -/
  structs : Array Struct := {}
  /--
  Mapping from types to its "structure id". We cache failures using `none`.
  `typeIdOf[type]` is `some id`, then `id < structs.size`. -/
  typeIdOf : PHashMap ExprPtr (Option Nat) := {}
  /- Mapping from expressions/terms to their structure ids. -/
  exprToStructId : PHashMap ExprPtr Nat := {}
  deriving Inhabited

builtin_initialize orderExt : SolverExtension State ← registerSolverExtension (return {})

def get' : GoalM State := do
  orderExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  orderExt.modifyState f

end Lean.Meta.Grind.Order
