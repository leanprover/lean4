/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ShareCommon
import Lean.Meta.Basic
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.Canonicalizer
import Lean.Meta.Tactic.Util

namespace Lean.Meta.Grind

structure Context where
  mainDeclName : Name

structure State where
  canon      : Canonicalizer.State := {}
  /-- `ShareCommon` (aka `Hashconsing`) state. -/
  scState    : ShareCommon.State.{0} ShareCommon.objectFactory := ShareCommon.State.mk _
  /-- Next index for creating auxiliary theorems. -/
  nextThmIdx : Nat := 1

abbrev GrindM := ReaderT Context $ StateRefT State MetaM

@[inline] def GrindM.run (x : GrindM α) (mainDeclName : Name) : MetaM α :=
  x { mainDeclName } |>.run' {}

def abstractNestedProofs (e : Expr) : GrindM Expr := do
  let nextIdx := (← get).nextThmIdx
  let (e, s') ← AbstractNestedProofs.visit e |>.run { baseName := (← read).mainDeclName } |>.run |>.run { nextIdx }
  modify fun s => { s with nextThmIdx := s'.nextIdx }
  return e

def shareCommon (e : Expr) : GrindM Expr := do
  modifyGet fun { canon, scState, nextThmIdx } =>
    let (e, scState) := ShareCommon.State.shareCommon scState e
    (e, { canon, scState, nextThmIdx })

def canon (e : Expr) : GrindM Expr := do
  let canonS ← modifyGet fun s => (s.canon, { s with canon := {} })
  let (e, canonS) ← Canonicalizer.CanonM.run (canonRec e) (s := canonS)
  modify fun s => { s with canon := canonS }
  return e
where
  canonRec (e : Expr) : CanonM Expr := do
    let post (e : Expr) : CanonM TransformStep := do
      if e.isApp then
        return .done (← Meta.canon e)
      else
        return .done e
    transform e post

/--
Stores information for a node in the egraph.
Each internalized expression `e` has an `ENode` associated with it.
-/
structure ENode where
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
  generation : Nat := 0
  /-- Modification time -/
  mt : Nat := 0
  -- TODO: see Lean 3 implementation

structure Clause where
  expr  : Expr
  proof : Expr
  deriving Inhabited

def mkInputClause (fvarId : FVarId) : MetaM Clause :=
  return { expr := (← fvarId.getType), proof := mkFVar fvarId }

structure NewEq where
  lhs   : Expr
  rhs   : Expr
  proof : Expr
  isHEq : Bool

structure Goal where
  mvarId       : MVarId
  clauses      : PArray Clause := {}
  enodes       : PHashMap USize ENode := {}
  newEqs       : Array NewEq := #[]
  /-- `inconsistent := true` if `ENode`s for `True` and `False` are in the same equivalence class. -/
  inconsistent : Bool := false
  /-- Goal modification time. -/
  gmt          : Nat := 0
  deriving Inhabited

def Goal.admit (goal : Goal) : MetaM Unit :=
  goal.mvarId.admit

abbrev GoalM := StateRefT Goal GrindM

@[inline] def GoalM.run (goal : Goal) (x : GoalM α) : GrindM (α × Goal) :=
  StateRefT'.run x goal

@[inline] def GoalM.run' (goal : Goal) (x : GoalM Unit) : GrindM Goal :=
  StateRefT'.run' (x *> get) goal

/--
Returns `some n` if `e` has already been "internalized" into the
Otherwise, returns `none`s.
-/
def getENode? (e : Expr) : GoalM (Option ENode) :=
  return (← get).enodes.find? (unsafe ptrAddrUnsafe e)

def setENode (e : Expr) (n : ENode) : GoalM Unit :=
  modify fun s => { s with enodes := s.enodes.insert (unsafe ptrAddrUnsafe e) n }

def mkENodeCore (e : Expr) (interpreted ctor : Bool) (generation : Nat) : GoalM Unit := do
  setENode e {
    next := e, root := e, cgRoot := e, size := 1
    flipped := false
    heqProofs := false
    hasLambdas := e.isLambda
    mt := (← get).gmt
    interpreted, ctor, generation
  }

def mkGoal (mvarId : MVarId) : GrindM Goal := do
  GoalM.run' { mvarId } do
    mkENodeCore (← shareCommon (mkConst ``True)) (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore (← shareCommon (mkConst ``False)) (interpreted := true) (ctor := false) (generation := 0)

end Lean.Meta.Grind
