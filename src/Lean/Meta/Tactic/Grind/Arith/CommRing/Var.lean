/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util

namespace Lean.Meta.Grind.Arith.CommRing

def mkVar (e : Expr) (ringId : Nat) : GoalM Var := do
  let s ← getRing ringId
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifyRing ringId fun s => { s with
    vars      := s.vars.push e
    varMap    := s.varMap.insert { expr := e } var
  }
  setTermRingId e ringId
  markAsCommRingTerm e
  return var

end Lean.Meta.Grind.Arith.CommRing
