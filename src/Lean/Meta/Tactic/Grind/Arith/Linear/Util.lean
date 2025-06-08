/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind.Arith.Linear

def get' : GoalM State := do
  return (← get).arith.linear

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.linear := f s.arith.linear }

structure LinearM.Context where
  structId : Nat

class MonadGetStruct (m : Type → Type) where
  getStruct : m Struct

export MonadGetStruct (getStruct)

@[always_inline]
instance (m n) [MonadLift m n] [MonadGetStruct m] : MonadGetStruct n where
  getStruct    := liftM (getStruct : m Struct)

/-- We don't want to keep carrying the `StructId` around. -/
abbrev LinearM := ReaderT LinearM.Context GoalM

abbrev LinearM.run (structId : Nat) (x : LinearM α) : GoalM α :=
  x { structId }

abbrev getStructId : LinearM Nat :=
  return (← read).structId

protected def LinearM.getStruct : LinearM Struct := do
  let s ← get'
  let structId ← getStructId
  if h : structId < s.structs.size then
    return s.structs[structId]
  else
    throwError "`grind` internal error, invalid structure id"

instance : MonadGetStruct LinearM where
  getStruct := LinearM.getStruct

@[inline] def modifyStruct (f : Struct → Struct) : LinearM Unit := do
  let structId ← getStructId
  modify' fun s => { s with structs := s.structs.modify structId f }

def getTermStructId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToStructId.find? { expr := e }

def setTermStructId (e : Expr) : LinearM Unit := do
  let structId ← getStructId
  if let some structId' ← getTermStructId? e then
    unless structId' == structId do
      reportIssue! "expression in two different structure in linarith module{indentExpr e}"
    return ()
  modify' fun s => { s with exprToStructId := s.exprToStructId.insert { expr := e } structId }

end Lean.Meta.Grind.Arith.Linear
