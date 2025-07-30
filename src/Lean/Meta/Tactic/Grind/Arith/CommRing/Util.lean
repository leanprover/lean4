/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Canon
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.SynthInstance
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

public section

namespace Lean.Meta.Grind.Arith.CommRing

def get' : GoalM State := do
  return (← get).arith.ring

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.ring := f s.arith.ring }

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

class MonadRing (m : Type → Type) where
  getRing : m Ring
  modifyRing : (Ring → Ring) → m Unit
  /--
  Helper function for removing dependency on `GoalM`.
  In `RingM` and `SemiringM`, this is just `sharedCommon (← canon e)`
  When printing counterexamples, we are at `MetaM`, and this is just the identity function.
  -/
  canonExpr : Expr → m Expr
  /--
  Helper function for removing dependency on `GoalM`. During search we
  want to track the instances synthesized by `grind`, and this is `Grind.synthInstance`.
  -/
  synthInstance? : Expr → m (Option Expr)

export MonadRing (getRing modifyRing canonExpr)

@[always_inline]
instance (m n) [MonadLift m n] [MonadRing m] : MonadRing n where
  getRing    := liftM (getRing : m Ring)
  modifyRing f := liftM (modifyRing f : m Unit)
  canonExpr e := liftM (canonExpr e : m Expr)
  synthInstance? e := liftM (MonadRing.synthInstance? e : m (Option Expr))

def MonadRing.synthInstance [Monad m] [MonadError m] [MonadRing m] (type : Expr) : m Expr := do
  let some inst ← synthInstance? type
    | throwError "`grind` failed to find instance{indentExpr type}"
  return inst

/-- We don't want to keep carrying the `RingId` around. -/
abbrev RingM := ReaderT RingM.Context GoalM

abbrev RingM.run (ringId : Nat) (x : RingM α) : GoalM α :=
  x { ringId }

abbrev getRingId : RingM Nat :=
  return (← read).ringId

protected def RingM.getRing : RingM Ring := do
  let s ← get'
  let ringId ← getRingId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

instance : MonadRing RingM where
  getRing := RingM.getRing
  modifyRing f := do
    let ringId ← getRingId
    modify' fun s => { s with rings := s.rings.modify ringId f }
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

structure SemiringM.Context where
  semiringId : Nat

abbrev SemiringM := ReaderT SemiringM.Context GoalM

abbrev SemiringM.run (semiringId : Nat) (x : SemiringM α) : GoalM α :=
  x { semiringId }

abbrev getSemiringId : SemiringM Nat :=
  return (← read).semiringId

def getSemiring : SemiringM Semiring := do
  let s ← get'
  let semiringId ← getSemiringId
  if h : semiringId < s.semirings.size then
    return s.semirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

protected def SemiringM.getRing : SemiringM Ring := do
  let s ← get'
  let ringId := (← getSemiring).ringId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

instance : MonadRing SemiringM where
  getRing := SemiringM.getRing
  modifyRing f := do
    let ringId := (← getSemiring).ringId
    modify' fun s => { s with rings := s.rings.modify ringId f }
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

@[inline] def modifySemiring (f : Semiring → Semiring) : SemiringM Unit := do
  let semiringId ← getSemiringId
  modify' fun s => { s with semirings := s.semirings.modify semiringId f }

abbrev withCheckCoeffDvd (x : RingM α) : RingM α :=
  withReader (fun ctx => { ctx with checkCoeffDvd := true }) x

def checkCoeffDvd : RingM Bool :=
  return (← read).checkCoeffDvd

def getTermRingId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToRingId.find? { expr := e }

def setTermRingId (e : Expr) : RingM Unit := do
  let ringId ← getRingId
  if let some ringId' ← getTermRingId? e then
    unless ringId' == ringId do
      reportIssue! "expression in two different rings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToRingId := s.exprToRingId.insert { expr := e } ringId }

def getTermSemiringId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToSemiringId.find? { expr := e }

def setTermSemiringId (e : Expr) : SemiringM Unit := do
  let semiringId ← getSemiringId
  if let some semiringId' ← getTermSemiringId? e then
    unless semiringId' == semiringId do
      reportIssue! "expression in two different semirings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToSemiringId := s.exprToSemiringId.insert { expr := e } semiringId }

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
  return (← getRing).noZeroDivInst?

/--
Returns `true` if the current ring satisfies the property
```
∀ (k : Nat) (a : α), k ≠ 0 → OfNat.ofNat (α := α) k * a = 0 → a = 0
```
-/
def noZeroDivisors : RingM Bool := do
  return (← getRing).noZeroDivInst?.isSome

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
  return (← getRing).fieldInst?.isSome

def isQueueEmpty : RingM Bool :=
  return (← getRing).queue.isEmpty

def getNext? : RingM (Option EqCnstr) := do
  let some c := (← getRing).queue.min? | return none
  modifyRing fun s => { s with queue := s.queue.erase c }
  incSteps
  return some c

variable [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadRing m]

private def mkUnaryFn (type : Expr) (u : Level) (instDeclName : Name) (declName : Name) : m Expr := do
  let inst ← MonadRing.synthInstance <| mkApp (mkConst instDeclName [u]) type
  canonExpr <| mkApp2 (mkConst declName [u]) type inst

private def mkBinHomoFn (type : Expr) (u : Level) (instDeclName : Name) (declName : Name) : m Expr := do
  let inst ← MonadRing.synthInstance <| mkApp3 (mkConst instDeclName [u, u, u]) type type type
  canonExpr <| mkApp4 (mkConst declName [u, u, u]) type type type inst

def getAddFn : m Expr := do
  let ring ← getRing
  if let some addFn := ring.addFn? then return addFn
  let addFn ← mkBinHomoFn ring.type ring.u ``HAdd ``HAdd.hAdd
  modifyRing fun s => { s with addFn? := some addFn }
  return addFn

def getSubFn : m Expr := do
  let ring ← getRing
  if let some subFn := ring.subFn? then return subFn
  let subFn ← mkBinHomoFn ring.type ring.u ``HSub ``HSub.hSub
  modifyRing fun s => { s with subFn? := some subFn }
  return subFn

def getMulFn : m Expr := do
  let ring ← getRing
  if let some mulFn := ring.mulFn? then return mulFn
  let mulFn ← mkBinHomoFn ring.type ring.u ``HMul ``HMul.hMul
  modifyRing fun s => { s with mulFn? := some mulFn }
  return mulFn

def getNegFn : m Expr := do
  let ring ← getRing
  if let some negFn := ring.negFn? then return negFn
  let negFn ← mkUnaryFn ring.type ring.u ``Neg ``Neg.neg
  modifyRing fun s => { s with negFn? := some negFn }
  return negFn

def getInvFn : m Expr := do
  let ring ← getRing
  if ring.fieldInst?.isNone then
    throwError "`grind` internal error, type is not a field{indentExpr ring.type}"
  if let some invFn := ring.invFn? then return invFn
  let invFn ← mkUnaryFn ring.type ring.u ``Inv ``Inv.inv
  modifyRing fun s => { s with invFn? := some invFn }
  return invFn

private def mkPowFn (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let inst ← MonadRing.synthInstance <| mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type
  let inst' := mkApp2 (mkConst ``Grind.Semiring.npow [u]) type semiringInst
  checkInst inst inst'
  canonExpr <| mkApp4 (mkConst ``HPow.hPow [u, 0, u]) type Nat.mkType type inst
where
  checkInst (inst inst' : Expr) : MetaM Unit := do
    unless (← withDefault <| isDefEq inst inst') do
      throwError "instance for power operator{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"

def getPowFn : m Expr := do
  let ring ← getRing
  if let some powFn := ring.powFn? then return powFn
  let powFn ← mkPowFn ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with powFn? := some powFn }
  return powFn

def getIntCastFn : m Expr := do
  let ring ← getRing
  if let some intCastFn := ring.intCastFn? then return intCastFn
  let inst' := mkApp2 (mkConst ``Grind.Ring.intCast [ring.u]) ring.type ring.ringInst
  let instType := mkApp (mkConst ``IntCast [ring.u]) ring.type
  -- Note that `Ring.intCast` is not registered as a global instance
  -- (to avoid introducing unwanted coercions)
  -- so merely having a `Ring α` instance
  -- does not guarantee that an `IntCast α` will be available.
  -- When both are present we verify that they are defeq,
  -- and otherwise fall back to the field of the `Ring α` instance that we already have.
  let inst ← match (← MonadRing.synthInstance? instType) with
    | none => pure inst'
    | some inst => checkInst inst inst'; pure inst
  let intCastFn ← canonExpr <| mkApp2 (mkConst ``IntCast.intCast [ring.u]) ring.type inst
  modifyRing fun s => { s with intCastFn? := some intCastFn }
  return intCastFn
where
  checkInst (inst inst' : Expr) : MetaM Unit := do
    unless (← withDefault <| isDefEq inst inst') do
      throwError "instance for intCast{indentExpr inst}\nis not definitionally equal to the `Grind.Ring` one{indentExpr inst'}"

private def mkNatCastFn (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let inst' := mkApp2 (mkConst ``Grind.Semiring.natCast [u]) type semiringInst
  let instType := mkApp (mkConst ``NatCast [u]) type
  -- Note that `Semiring.natCast` is not registered as a global instance
  -- (to avoid introducing unwanted coercions)
  -- so merely having a `Semiring α` instance
  -- does not guarantee that an `NatCast α` will be available.
  -- When both are present we verify that they are defeq,
  -- and otherwise fall back to the field of the `Semiring α` instance that we already have.
  let inst ← match (← MonadRing.synthInstance? instType) with
  | none => pure inst'
  | some inst => checkInst inst inst'; pure inst
  canonExpr <| mkApp2 (mkConst ``NatCast.natCast [u]) type inst
where
  checkInst (inst inst' : Expr) : MetaM Unit := do
    unless (← withDefault <| isDefEq inst inst') do
      throwError "instance for natCast{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"

def getNatCastFn : m Expr := do
  let ring ← getRing
  if let some natCastFn := ring.natCastFn? then return natCastFn
  let natCastFn ← mkNatCastFn ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with natCastFn? := some natCastFn }
  return natCastFn

private def mkOne (u : Level) (type : Expr) (semiringInst : Expr) : m Expr := do
  let n := mkRawNatLit 1
  let ofNatInst := mkApp3 (mkConst ``Grind.Semiring.ofNat [u]) type semiringInst n
  canonExpr <| mkApp3 (mkConst ``OfNat.ofNat [u]) type n ofNatInst

def getOne [MonadLiftT GoalM m] : m Expr := do
  let ring ← getRing
  if let some one := ring.one? then return one
  let one ← mkOne ring.u ring.type ring.semiringInst
  modifyRing fun s => { s with one? := some one }
  internalize one 0
  return one

def getAddFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some addFn := s.addFn? then return addFn
  let addFn ← mkBinHomoFn s.type s.u ``HAdd ``HAdd.hAdd
  modifySemiring fun s => { s with addFn? := some addFn }
  return addFn

def getMulFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some mulFn := s.mulFn? then return mulFn
  let mulFn ← mkBinHomoFn s.type s.u ``HMul ``HMul.hMul
  modifySemiring fun s => { s with mulFn? := some mulFn }
  return mulFn

def getPowFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some powFn := s.powFn? then return powFn
  let powFn ← mkPowFn s.u s.type s.semiringInst
  modifySemiring fun s => { s with powFn? := some powFn }
  return powFn

def getNatCastFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some natCastFn := s.natCastFn? then return natCastFn
  let natCastFn ← mkNatCastFn s.u s.type s.semiringInst
  modifySemiring fun s => { s with natCastFn? := some natCastFn }
  return natCastFn

def getToQFn : SemiringM Expr := do
  let s ← getSemiring
  if let some toQFn := s.toQFn? then return toQFn
  let toQFn ← canonExpr <| mkApp2 (mkConst ``Grind.Ring.OfSemiring.toQ [s.u]) s.type s.semiringInst
  modifySemiring fun s => { s with toQFn? := some toQFn }
  return toQFn

private def mkAddRightCancelInst? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let add := mkApp (mkConst ``Add [u]) type
  let some addInst ← synthInstance? add | return none
  let addRightCancel := mkApp2 (mkConst ``Grind.AddRightCancel [u]) type addInst
  synthInstance? addRightCancel

def getAddRightCancelInst? : SemiringM (Option Expr) := do
  let s ← getSemiring
  if let some r := s.addRightCancelInst? then return r
  let addRightCancelInst? ← mkAddRightCancelInst? s.u s.type
  modifySemiring fun s => { s with addRightCancelInst? := some addRightCancelInst? }
  return addRightCancelInst?

end Lean.Meta.Grind.Arith.CommRing
