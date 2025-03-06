/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat
/--
In principle, we only need to support two kinds of case split.
- Disequalities.
- Cooper-Left, but we have 4 different variants of this one.
-/
inductive CaseKind where
  | diseq (d : DiseqCnstr)
  | cooper (s : CooperSplitPred) (hs : Array (FVarId × UnsatProof)) (decVars : FVarIdSet)
  deriving Inhabited

structure Case where
  kind   : CaseKind
  /--
  Decision variable used to represent the case-split.
  For example, suppose we are splitting on `p ≠ 0`. Then,
  we create a decision variable `h : p + 1 ≤ 0`
  -/
  fvarId : FVarId
  /--
  Snapshot of the cutsat state for backtracking purposes.
  We do not use a trail stack.
  -/
  saved  : State
  deriving Inhabited

inductive Search.Kind where
  | /--
    Allow variables to be assigned to rational numbers during model
    construction.
    -/
    rat
  | /--
    Variables must be assigned to integer numbers.
    Cooper case splits are required in this mode.
    -/
    int
  deriving Inhabited, BEq

/--
State of the model search procedure.
-/
structure Search.State where
  /-- Decision stack (aka case-split stack) -/
  cases   : PArray Case := {}
  /-- `precise := false` if not all constraints were satisfied during the search. -/
  precise : Bool := true
  /-- Set of decision variables in `cases`. -/
  decVars : FVarIdSet := {}

abbrev SearchM := ReaderT Search.Kind (StateRefT Search.State GoalM)

/-- Returns `true` if approximations are allowed. -/
def isApprox : SearchM Bool :=
  return (← read) == .rat

/-- Sets `precise` to `false` to indicate that some constraint was not satisfied. -/
def setImprecise : SearchM Unit := do
  modify fun s => { s with precise := false }

def mkCase (kind : CaseKind) : SearchM FVarId := do
  let fvarId ← mkFreshFVarId
  let saved ← get'
  modify fun s => { s with
    cases   := s.cases.push { saved, fvarId, kind }
    decVars := s.decVars.insert fvarId
  }
  modify' fun s => { s with caseSplits := true }
  trace[grind.debug.cutsat.backtrack] "mkCase fvarId: {fvarId.name}"
  return fvarId

end Lean.Meta.Grind.Arith.Cutsat
