/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.Types
public import Lean.Meta.Sym.Arith.Types
public section
namespace Lean.Meta.Grind.Order

structure OrderM.Context where
  structId : Nat

abbrev OrderM := ReaderT OrderM.Context GoalM

abbrev OrderM.run (structId : Nat) (x : OrderM α) : GoalM α :=
  x { structId }

abbrev getStructId : OrderM Nat :=
  return (← read).structId

/-- The `Sym.Arith` classification record (instances, `≤`/`<` functions) of the current order. -/
def getOrder : OrderM Sym.Arith.Order := do
  let s ← Sym.Arith.getArithState
  let structId ← getStructId
  if h : structId < s.orders.size then
    return s.orders[structId]
  else
    throwError "`grind` internal error, invalid order structure id"

/-- The per-goal solver state of the current order; empty if this goal has not used it yet. -/
def getStruct : OrderM Struct := do
  let structId ← getStructId
  return (← get').structs.getD structId { id := structId }

def modifyStruct (f : Struct → Struct) : OrderM Unit := do
  let structId ← getStructId
  modify' fun s => { s with structs := (s.structs.rightpad (structId + 1) { id := structId }).modify structId f }

def getExpr (u : NodeId) : OrderM Expr := do
  return (← getStruct).nodes[u]!

def getDist? (u v : NodeId) : OrderM (Option Weight) := do
  return (← getStruct).targets[u]!.find? v

def getProof? (u v : NodeId) : OrderM (Option ProofInfo) := do
  return (← getStruct).proofs[u]!.find? v

def getNodeId (e : Expr) : OrderM NodeId := do
  let some nodeId := (← getStruct).nodeMap.find? { expr := e }
    | throwError "internal `grind` error, term has not been internalized by order module{indentExpr e}"
  return nodeId

def getProof (u v : NodeId) : OrderM ProofInfo := do
  let some p ← getProof? u v
    | throwError "internal `grind` error, failed to construct proof for{indentExpr (← getExpr u)}\nand{indentExpr (← getExpr v)}"
  return p

def getCnstr? (e : Expr) : OrderM (Option (Cnstr NodeId)) :=
  return (← getStruct).cnstrs.find? { expr := e }

def isRing : OrderM Bool :=
  return (← getOrder).ringId?.isSome

def isPartialOrder : OrderM Bool :=
  return (← getOrder).isPartialInst?.isSome

def isLinearPreorder : OrderM Bool :=
  return (← getOrder).isLinearPreInst?.isSome

def hasLt : OrderM Bool :=
  return (← getOrder).lawfulOrderLTInst?.isSome

def isInt : OrderM Bool :=
  return isSameExpr (← getOrder).type (← getIntExpr)

end Lean.Meta.Grind.Order
