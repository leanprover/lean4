/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Util
public import Lean.Meta.Tactic.Grind.Main
public section
namespace Lean.Meta.Sym
open Grind (Params)

def SymM.run (x : SymM α) (params : Params) : MetaM α := do
  x.run' {} |>.run params

def SymM.run' (x : SymM α) (config : Grind.Config := {}) : MetaM α := do
  let params ← Grind.mkDefaultParams config
  x.run params

/-- Creates a new goal using the given metavariable -/
def mkGoal (mvarId : MVarId) : SymM Goal := do
  let mvarId ← preprocessMVar mvarId
  Grind.mkGoal mvarId

/-- Internalizes the next `num` hypotheses into `grind`. -/
def internalizeNumHypotheses (goal : Goal) (num : Nat) : SymM Goal := do
  Grind.processHypotheses goal (some num)

/-- Internalizes all pending hypotheses into `grind`. -/
def internalizeAllHypotheses (goal : Goal) : SymM Goal := do
  Grind.processHypotheses goal none

end Lean.Meta.Sym
