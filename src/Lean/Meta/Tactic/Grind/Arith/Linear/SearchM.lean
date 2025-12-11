/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
public section
namespace Lean.Meta.Grind.Arith.Linear

structure Case where
  c : DiseqCnstr
  /--
  Decision variable used to represent the case-split.
  For example, suppose we are splitting on `p ≠ 0`. Then,
  we create a decision variable `h : p < 0`
  -/
  fvarId : FVarId
  /--
  Snapshot of the state for backtracking purposes.
  We do not use a trail stack.
  -/
  saved  : Struct
  deriving Inhabited

/--
State of the model search procedure.
-/
structure Search.State where
  /-- Decision stack (aka case-split stack) -/
  cases   : PArray Case := {}
  /-- Set of decision variables in `cases`. -/
  decVars : FVarIdSet := {}

abbrev SearchM := StateRefT Search.State LinearM

def mkCase (c : DiseqCnstr) : SearchM FVarId := do
  let fvarId ← mkFreshFVarId
  let saved ← getStruct
  modify fun s => { s with
    cases   := s.cases.push { saved, fvarId, c }
    decVars := s.decVars.insert fvarId
  }
  modifyStruct fun s => { s with caseSplits := true }
  return fvarId

end Lean.Meta.Grind.Arith.Linear
