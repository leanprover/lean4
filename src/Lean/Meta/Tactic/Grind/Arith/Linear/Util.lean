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

def getNoNatDivInst : LinearM Expr := do
  let some inst := (← getStruct).noNatDivInst?
    | throwError "`grind linarith` internal error, structure does not implement `NoNatZeroDivisors`"
  return inst

def getPreorderInst : LinearM Expr := do
  let some inst := (← getStruct).preorderInst?
    | throwError "`grind linarith` internal error, structure is not a preorder"
  return inst

def getIsOrdInst : LinearM Expr := do
  let some inst := (← getStruct).isOrdInst?
    | throwError "`grind linarith` internal error, structure is not an ordered module"
  return inst

def isOrdered : LinearM Bool :=
  return (← getStruct).isOrdInst?.isSome

def getLtFn [Monad m] [MonadError m] [MonadGetStruct m] : m Expr := do
  let some lt := (← getStruct).ltFn?
    | throwError "`grind linarith` internal error, structure is not an ordered module"
  return lt

def getLeFn [Monad m] [MonadError m] [MonadGetStruct m] : m Expr := do
  let some le := (← getStruct).leFn?
    | throwError "`grind linarith` internal error, structure is not an ordered int module"
  return le

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

/-- Returns `true` if the linarith state is inconsistent. -/
def inconsistent : LinearM Bool := do
  if (← isInconsistent) then return true
  return (← getStruct).conflict?.isSome

/-- Returns `true` if `x` has been eliminated using an equality constraint. -/
def eliminated (x : Var) : LinearM Bool :=
  return (← getStruct).elimEqs[x]!.isSome

/-- Returns occurrences of `x`. -/
def getOccursOf (x : Var) : LinearM VarSet :=
  return (← getStruct).occurs[x]!

/--
Adds `y` as an occurrence of `x`.
That is, `x` occurs in `lowers[y]`, `uppers[y]`, or `diseqs[y]`.
-/
def addOcc (x : Var) (y : Var) : LinearM Unit := do
  unless (← getOccursOf x).contains y do
    modifyStruct fun s => { s with occurs := s.occurs.modify x fun ys => ys.insert y }

/--
Given `p` a polynomial being inserted into `lowers`, `uppers`, or `diseqs`,
get its leading variable `y`, and adds `y` as an occurrence for the remaining variables in `p`.
-/
partial def _root_.Lean.Grind.Linarith.Poly.updateOccs (p : Poly) : LinearM Unit := do
  let .add _ y p := p | throwError "`grind linarith` internal error, unexpected constant polynomial"
  let rec go (p : Poly) : LinearM Unit := do
    let .add _ x p := p | return ()
    addOcc x y; go p
  go p

/--
Given a polynomial `p`, returns `some (x, k, c)` if `p` contains the monomial `k*x`,
and `x` has been eliminated using the equality `c`.
-/
def _root_.Lean.Grind.Linarith.Poly.findVarToSubst (p : Poly) : LinearM (Option (Int × Var × EqCnstr)) := do
  match p with
  | .nil => return none
  | .add k x p =>
    if let some c := (← getStruct).elimEqs[x]! then
      return some (k, x, c)
    else
      findVarToSubst p

def _root_.Lean.Grind.Linarith.Poly.gcdCoeffsAux : Poly → Nat → Nat
  | .nil, k => k
  | .add k' _ p, k => gcdCoeffsAux p (Int.gcd k' k)

def _root_.Lean.Grind.Linarith.Poly.gcdCoeffs (p : Poly) : Nat :=
  match p with
  | .add k _ p => p.gcdCoeffsAux k.natAbs
  | .nil => 1

def _root_.Lean.Grind.Linarith.Poly.div (p : Poly) (k : Int) : Poly :=
  match p with
  | .add a x p => .add (a / k) x (p.div k)
  | .nil => .nil

/--
Selects the variable in the given linear polynomial whose coefficient has the smallest absolute value.
-/
def _root_.Lean.Grind.Linarith.Poly.pickVarToElim? (p : Poly) : Option (Int × Var) :=
  match p with
  | .nil => none
  | .add k x p => go k x p
where
  go (k : Int) (x : Var) (p : Poly) : Int × Var :=
    if k == 1 || k == -1 then
      (k, x)
    else match p with
      | .nil => (k, x)
      | .add k' x' p => if k'.natAbs < k.natAbs then go k' x' p else go k x p

end Lean.Meta.Grind.Arith.Linear
