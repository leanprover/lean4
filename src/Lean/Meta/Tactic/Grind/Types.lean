/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ShareCommon
import Lean.Meta.Basic
import Lean.Meta.CongrTheorems
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Util

namespace Lean.Meta.Grind

@[inline] def isSameExpr (a b : Expr) : Bool :=
  -- It is safe to use pointer equality because we hashcons all expressions
  -- inserted into the E-graph
  unsafe ptrEq a b

structure Context where
  mainDeclName : Name

/--
Key for the congruence theorem cache.
-/
structure CongrTheoremCacheKey where
  f       : Expr
  numArgs : Nat

-- We manually define `BEq` because we wannt to use pointer equality.
instance : BEq CongrTheoremCacheKey where
  beq a b := isSameExpr a.f b.f && a.numArgs == b.numArgs

-- We manually define `Hashable` because we wannt to use pointer equality.
instance : Hashable CongrTheoremCacheKey where
  hash a := mixHash (unsafe ptrAddrUnsafe a.f).toUInt64 (hash a.numArgs)

structure State where
  canon      : Canon.State := {}
  /-- `ShareCommon` (aka `Hashconsing`) state. -/
  scState    : ShareCommon.State.{0} ShareCommon.objectFactory := ShareCommon.State.mk _
  /-- Next index for creating auxiliary theorems. -/
  nextThmIdx : Nat := 1
  /--
  Congruence theorems generated so far. Recall that for constant symbols
  we rely on the reserved name feature (i.e., `mkHCongrWithArityForConst?`).
  Remark: we currently do not reuse congruence theorems
  -/
  congrThms  : PHashMap CongrTheoremCacheKey CongrTheorem := {}
  trueExpr   : Expr
  falseExpr  : Expr

abbrev GrindM := ReaderT Context $ StateRefT State MetaM

def GrindM.run (x : GrindM α) (mainDeclName : Name) : MetaM α := do
  let scState := ShareCommon.State.mk _
  let (falseExpr, scState) := ShareCommon.State.shareCommon scState (mkConst ``False)
  let (trueExpr, scState)  := ShareCommon.State.shareCommon scState (mkConst ``True)
  x { mainDeclName } |>.run' { scState, trueExpr, falseExpr }

def getTrueExpr : GrindM Expr := do
  return (← get).trueExpr

def getFalseExpr : GrindM Expr := do
  return (← get).falseExpr

def getMainDeclName : GrindM Name :=
  return (← read).mainDeclName

/--
Abtracts nested proofs in `e`. This is a preprocessing step performed before internalization.
-/
def abstractNestedProofs (e : Expr) : GrindM Expr := do
  let nextIdx := (← get).nextThmIdx
  let (e, s') ← AbstractNestedProofs.visit e |>.run { baseName := (← getMainDeclName) } |>.run |>.run { nextIdx }
  modify fun s => { s with nextThmIdx := s'.nextIdx }
  return e

/--
Applies hash-consing to `e`. Recall that all expressions in a `grind` goal have
been hash-consing. We perform this step before we internalize expressions.
-/
def shareCommon (e : Expr) : GrindM Expr := do
  modifyGet fun { canon, scState, nextThmIdx, congrThms, trueExpr, falseExpr } =>
    let (e, scState) := ShareCommon.State.shareCommon scState e
    (e, { canon, scState, nextThmIdx, congrThms, trueExpr, falseExpr })

/--
Canonicalizes nested types, type formers, and instances in `e`.
-/
def canon (e : Expr) : GrindM Expr := do
  let canonS ← modifyGet fun s => (s.canon, { s with canon := {} })
  let (e, canonS) ← Canon.canon e |>.run canonS
  modify fun s => { s with canon := canonS }
  return e

/--
Creates a congruence theorem for a `f`-applications with `numArgs` arguments.
-/
def mkHCongrWithArity (f : Expr) (numArgs : Nat) : GrindM CongrTheorem := do
  let key := { f, numArgs }
  if let some result := (← get).congrThms.find? key then
    return result
  if let .const declName us := f then
    if let some result ← mkHCongrWithArityForConst? declName us numArgs then
      modify fun s => { s with congrThms := s.congrThms.insert key result }
      return result
  let result ← Meta.mkHCongrWithArity f numArgs
  modify fun s => { s with congrThms := s.congrThms.insert key result }
  return result

/--
Stores information for a node in the egraph.
Each internalized expression `e` has an `ENode` associated with it.
-/
structure ENode where
  /-- Node represented by this ENode. -/
  self : Expr
  /-- Next element in the equivalence class. -/
  next : Expr
  /-- Root (aka canonical representative) of the equivalence class -/
  root : Expr
  /-- Root of the congruence class. This is field is a don't care if `e` is not an application. -/
  cgRoot : Expr
  /--
  When `e` was added to this equivalence class because of an equality `h : e = target`,
  then we store `target` here, and `h` at `proof?`.
  -/
  target? : Option Expr := none
  proof? : Option Expr := none
  /-- Proof has been flipped. -/
  flipped : Bool := false
  /-- Number of elements in the equivalence class, this field is meaningless if node is not the root. -/
  size : Nat := 1
  /-- `interpreted := true` if node should be viewed as an abstract value. -/
  interpreted : Bool := false
  /-- `ctor := true` if the head symbol is a constructor application. -/
  ctor : Bool := false
  /-- `hasLambdas := true` if equivalence class contains lambda expressions. -/
  hasLambdas : Bool := false
  /--
  If `heqProofs := true`, then some proofs in the equivalence class are based
  on heterogeneous equality.
  -/
  heqProofs : Bool := false
  /--
  Unique index used for pretty printing and debugging purposes.
  -/
  idx : Nat := 0
  generation : Nat := 0
  /-- Modification time -/
  mt : Nat := 0
  -- TODO: see Lean 3 implementation
  deriving Inhabited, Repr

structure NewEq where
  lhs   : Expr
  rhs   : Expr
  proof : Expr
  isHEq : Bool

structure Goal where
  mvarId       : MVarId
  enodes       : PHashMap USize ENode := {}
  /-- Equations to be processed. -/
  newEqs       : Array NewEq := #[]
  /-- `inconsistent := true` if `ENode`s for `True` and `False` are in the same equivalence class. -/
  inconsistent : Bool := false
  /-- Goal modification time. -/
  gmt          : Nat := 0
  /-- Next unique index for creating ENodes -/
  nextIdx      : Nat := 0
  deriving Inhabited

def Goal.admit (goal : Goal) : MetaM Unit :=
  goal.mvarId.admit

abbrev GoalM := StateRefT Goal GrindM

@[inline] def GoalM.run (goal : Goal) (x : GoalM α) : GrindM (α × Goal) :=
  goal.mvarId.withContext do StateRefT'.run x goal

@[inline] def GoalM.run' (goal : Goal) (x : GoalM Unit) : GrindM Goal :=
  goal.mvarId.withContext do StateRefT'.run' (x *> get) goal

/--
Returns `some n` if `e` has already been "internalized" into the
Otherwise, returns `none`s.
-/
def getENode? (e : Expr) : GoalM (Option ENode) :=
  return (← get).enodes.find? (unsafe ptrAddrUnsafe e)

/-- Returns node associated with `e`. It assumes `e` has already been internalized. -/
def getENode (e : Expr) : GoalM ENode := do
  let some n := (← get).enodes.find? (unsafe ptrAddrUnsafe e) | unreachable!
  return n

/-- Returns the root element in the equivalence class of `e`. -/
def getRoot (e : Expr) : GoalM Expr :=
  return (← getENode e).root

/-- Returns the next element in the equivalence class of `e`. -/
def getNext (e : Expr) : GoalM Expr :=
  return (← getENode e).next

/-- Returns `true` if `e` has already been internalized. -/
def alreadyInternalized (e : Expr) : GoalM Bool :=
  return (← get).enodes.contains (unsafe ptrAddrUnsafe e)

def setENode (e : Expr) (n : ENode) : GoalM Unit :=
  modify fun s => { s with enodes := s.enodes.insert (unsafe ptrAddrUnsafe e) n }

def mkENodeCore (e : Expr) (interpreted ctor : Bool) (generation : Nat) : GoalM Unit := do
  setENode e {
    self := e, next := e, root := e, cgRoot := e, size := 1
    flipped := false
    heqProofs := false
    hasLambdas := e.isLambda
    mt := (← get).gmt
    idx := (← get).nextIdx
    interpreted, ctor, generation
  }
  modify fun s => { s with nextIdx := s.nextIdx + 1 }

def mkGoal (mvarId : MVarId) : GrindM Goal := do
  let trueExpr ← getTrueExpr
  let falseExpr ← getFalseExpr
  GoalM.run' { mvarId } do
    mkENodeCore falseExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore trueExpr (interpreted := true) (ctor := false) (generation := 0)

def forEachENode (f : ENode → GoalM Unit) : GoalM Unit := do
  -- We must sort because we are using pointer addresses to hash
  let nodes := (← get).enodes.toArray.map (·.2)
  let nodes := nodes.qsort fun a b => a.idx < b.idx
  for n in nodes do
    f n

def filterENodes (p : ENode → GoalM Bool) : GoalM (Array ENode) := do
  let ref ← IO.mkRef #[]
  forEachENode fun n => do
    if (← p n) then
      ref.modify (·.push n)
  ref.get

end Lean.Meta.Grind
