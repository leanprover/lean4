/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Linear.Util

namespace Lean.Meta.Grind.Arith.Linear

def mkVar (e : Expr) : LinearM Var := do
  let s ← getStruct
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifyStruct fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
    lowers     := s.lowers.push {}
    uppers     := s.lowers.push {}
    diseqs     := s.diseqs.push {}
    notIneqs   := s.notIneqs.push {}
    elimEqs    := s.elimEqs.push none
  }
  setTermStructId e
  -- TODO: markAsLinearTerm e
  return var

end Lean.Meta.Grind.Arith.Linear
