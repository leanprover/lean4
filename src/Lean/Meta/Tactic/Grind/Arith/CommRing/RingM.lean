/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.SynthInstance
public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
public import Lean.Meta.Sym.Arith.Ring.SymExt
public section
namespace Lean.Meta.Grind.Arith.CommRing

def checkMaxSteps : GoalM Bool := do
  return (← get').steps >= (← getConfig).ringSteps

def incSteps : GoalM Unit := do
  modify' fun s => { s with steps := s.steps + 1 }

structure RingM.Context where
  ringId : Nat
  /--
  If `checkCoeffDvd` is `true`, then when using a polynomial `k*m - p`
  to simplify `.. + k'*m*m_2 + ...`, the substitution is performed IF
  - `k` divides `k'`, OR
  - Ring implements `NoNatZeroDivisors`.

  We need this check when simplifying disequalities. In this case, if we perform
  the simplification anyway, we may end up with a proof that `k * q = 0`, but
  we cannot deduce `q = 0` since the ring does not implement `NoNatZeroDivisors`
  See comment at `PolyDerivation`.
  -/
  checkCoeffDvd : Bool := false

/-- We don't want to keep carrying the `RingId` around. -/
abbrev RingM := ReaderT RingM.Context GoalM

abbrev RingM.run (ringId : Nat) (x : RingM α) : GoalM α :=
  x { ringId }

abbrev getRingId : RingM Nat :=
  return (← read).ringId

instance : MonadCanon RingM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

protected def RingM.getCommRing : RingM CommRing := do
  let s ← get'
  let ringId ← getRingId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def RingM.modifyCommRing (f : CommRing → CommRing) : RingM Unit := do
  let ringId ← getRingId
  modify' fun s => { s with rings := s.rings.modify ringId f }

instance : MonadCommRing RingM where
  getCommRing := RingM.getCommRing
  modifyCommRing := RingM.modifyCommRing

/--
`MonadRing` for grind's `RingM`. Reads lazy ops (`addFn?`, etc.) from the shared
`arithRingExt` state, and per-context fields (`vars`, `varMap`, `denote`) from
grind's local `CommRing`. Writes are routed to the appropriate state.
-/
instance : Sym.Arith.Ring.MonadRing RingM where
  getRing := do
    let ringId ← getRingId
    let s ← Sym.Arith.Ring.arithRingExt.getState
    let sharedRing := s.rings[ringId]!.toRing
    let localRing := (← RingM.getCommRing).toRing
    return { sharedRing with vars := localRing.vars, varMap := localRing.varMap, denote := localRing.denote }
  modifyRing f := do
    let ringId ← getRingId
    let s ← Sym.Arith.Ring.arithRingExt.getState
    let sharedRing := s.rings[ringId]!.toRing
    let localRing := (← RingM.getCommRing).toRing
    let combined : Sym.Arith.Ring.Ring :=
      { sharedRing with vars := localRing.vars, varMap := localRing.varMap, denote := localRing.denote }
    let new := f combined
    -- Write lazy ops to shared state
    Sym.Arith.Ring.arithRingExt.modifyState fun s => { s with rings := s.rings.modify ringId fun r =>
      { r with toRing := { r.toRing with
        addFn? := new.addFn?, mulFn? := new.mulFn?, subFn? := new.subFn?,
        negFn? := new.negFn?, powFn? := new.powFn?, intCastFn? := new.intCastFn?,
        natCastFn? := new.natCastFn?, one? := new.one?
      }}
    }
    -- Write per-context to grind local
    RingM.modifyCommRing fun s => { s with toRing := { s.toRing with
      vars := new.vars, varMap := new.varMap, denote := new.denote
    }}

abbrev withCheckCoeffDvd (x : RingM α) : RingM α :=
  withReader (fun ctx => { ctx with checkCoeffDvd := true }) x

def checkCoeffDvd : RingM Bool :=
  return (← read).checkCoeffDvd

def getTermRingId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToRingId.find? { expr := e }

/-- Returns `some c` if the current ring has a nonzero characteristic `c`. -/
def nonzeroChar? [Monad m] [MonadRing m] : m (Option Nat) := do
  if let some (_, c) := (← getRing).charInst? then
    if c != 0 then
      return some c
  return none

/-- Returns `some (charInst, c)` if the current ring has a nonzero characteristic `c`. -/
def nonzeroCharInst? [Monad m] [MonadRing m] : m (Option (Expr × Nat)) := do
  if let some (inst, c) := (← getRing).charInst? then
    if c != 0 then
      return some (inst, c)
  return none

def noZeroDivisorsInst? : RingM (Option Expr) := do
  return (← getCommRing).noZeroDivInst?

/--
Returns `true` if the current ring satisfies the property
```
∀ (k : Nat) (a : α), k ≠ 0 → OfNat.ofNat (α := α) k * a = 0 → a = 0
```
-/
def noZeroDivisors : RingM Bool := do
  return (← getCommRing).noZeroDivInst?.isSome

/-- Returns `true` if the current ring has a `IsCharP` instance. -/
def hasChar  : RingM Bool := do
  return (← getRing).charInst?.isSome

/--
Returns the pair `(charInst, c)`. If the ring does not have a `IsCharP` instance, then throws internal error.
-/
def getCharInst : RingM (Expr × Nat) := do
  let some c := (← getRing).charInst?
    | throwError "`grind` internal error, ring does not have a characteristic"
  return c

def isField : RingM Bool :=
  return (← getCommRing).fieldInst?.isSome

def isQueueEmpty : RingM Bool :=
  return (← getCommRing).queue.isEmpty

def getNext? : RingM (Option EqCnstr) := do
  let some c := (← getCommRing).queue.min? | return none
  modifyCommRing fun s => { s with queue := s.queue.erase c }
  incSteps
  return some c

class MonadSetTermId (m : Type → Type) where
  setTermId : Expr → m Unit

def setTermRingId (e : Expr) : RingM Unit := do
  let ringId ← getRingId
  if let some ringId' ← getTermRingId? e then
    unless ringId' == ringId do
      reportIssue! "expression in two different rings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToRingId := s.exprToRingId.insert { expr := e } ringId }

def mkVarCore [MonadLiftT GoalM m] [Monad m] [MonadRing m] [MonadSetTermId m] (e : Expr) : m Var := do
  let s ← getRing
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifyRing fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  MonadSetTermId.setTermId e
  ringExt.markTerm e
  return var

instance : MonadSetTermId RingM where
  setTermId e := setTermRingId e

def mkVar (e : Expr) : RingM Var :=
  mkVarCore e

end Lean.Meta.Grind.Arith.CommRing
