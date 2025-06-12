/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util

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

open CommRing

def getRingCore? (ringId? : Option Nat) : GoalM (Option Ring) := do
  let some ringId := ringId? | return none
  RingM.run ringId do return some (← getRing)

def throwNotRing : LinearM α :=
  throwError "`grind linarith` internal error, structure is not a ring"

def throwNotCommRing : LinearM α :=
  throwError "`grind linarith` internal error, structure is not a commutative ring"

def getRing? : LinearM (Option Ring) := do
  getRingCore? (← getStruct).ringId?

def getRing : LinearM Ring := do
  let some ring ← getRing?
    | throwNotCommRing
  return ring

instance : MonadGetRing LinearM where
  getRing := Linear.getRing

def getZero : LinearM Expr :=
  return (← getStruct).zero

def getOne : LinearM Expr := do
  let some one := (← getStruct).one?
    | throwNotRing
  return one

def withRingM (x : RingM α) : LinearM α := do
  let some ringId := (← getStruct).ringId?
    | throwNotCommRing
  RingM.run ringId x

def isCommRing : LinearM Bool :=
  return (← getStruct).ringId?.isSome

def isOrderedCommRing : LinearM Bool := do
  return (← isCommRing) && (← getStruct).ringIsOrdInst?.isSome

def isLinearOrder : LinearM Bool :=
  return (← getStruct).linearInst?.isSome

def hasNoNatZeroDivisors : LinearM Bool :=
  return (← getStruct).noNatDivInst?.isSome

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

def getLinearOrderInst : LinearM Expr := do
  let some inst := (← getStruct).linearInst?
    | throwError "`grind linarith` internal error, structure is not a linear order"
  return inst

def getRingInst : LinearM Expr := do
  let some inst := (← getStruct).ringInst?
    | throwError "`grind linarith` internal error, structure is not a ring"
  return inst

def getCommRingInst : LinearM Expr := do
  let some inst := (← getStruct).commRingInst?
    | throwError "`grind linarith` internal error, structure is not a commutative ring"
  return inst

def getRingIsOrdInst : LinearM Expr := do
  let some inst := (← getStruct).ringIsOrdInst?
    | throwError "`grind linarith` internal error, structure is not an ordered ring"
  return inst

/--
Tries to evaluate the polynomial `p` using the partial model/assignment built so far.
The result is `none` if the polynomial contains variables that have not been assigned.
-/
def _root_.Lean.Grind.Linarith.Poly.eval? (p : Poly) : LinearM (Option Rat) := do
  let a := (← getStruct).assignment
  let rec go (v : Rat) : Poly → Option Rat
    | .nil => some v
    | .add k x p =>
      if _ : x < a.size then
        go (v + k*a[x]) p
      else
        none
  return go 0 p
/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def IneqCnstr.satisfied (c : IneqCnstr) : LinearM LBool := do
  let some v ← c.p.eval? | return .undef
  if c.strict then
    return decide (v < 0) |>.toLBool
  else
    return decide (v <= 0) |>.toLBool

def DiseqCnstr.satisfied (c : DiseqCnstr) : LinearM LBool := do
  let some v ← c.p.eval? | return .undef
  return decide (v != 0) |>.toLBool

/-- Resets the assignment of any variable bigger or equal to `x`. -/
def resetAssignmentFrom (x : Var) : LinearM Unit := do
  modifyStruct fun s => { s with assignment := shrink s.assignment x }

def getVar (x : Var) : LinearM Expr :=
  return (← getStruct).vars[x]!

end Lean.Meta.Grind.Arith.Linear
