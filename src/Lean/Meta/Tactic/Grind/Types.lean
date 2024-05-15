/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.Tactic.Util

namespace Lean.Meta.Grind

structure Clause where
  expr  : Expr
  proof : Expr
  deriving Inhabited

def mkInputClause (fvarId : FVarId) : MetaM Clause :=
  return { expr := (← fvarId.getType), proof := mkFVar fvarId }

structure Goal where
  mvarId  : MVarId
  clauses : PArray Clause := {}
  deriving Inhabited

def mkGoal (mvarId : MVarId) : Goal :=
  { mvarId }

def Goal.admit (goal : Goal) : MetaM Unit :=
  goal.mvarId.admit

end Lean.Meta.Grind
