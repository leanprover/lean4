/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util

namespace Lean.Meta.Grind.Arith.CommRing

def mkVar (e : Expr) : RingM Var := do
  let s ← getRing
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifyRing fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  setTermRingId e
  markAsCommRingTerm e
  return var

/-- Similar to `mkVar` but for `Semiring`s -/
def mkSVar (e : Expr) : SemiringM Var := do
  let s ← getSemiring
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifySemiring fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  setTermSemiringId e
  markAsCommRingTerm e
  return var

end Lean.Meta.Grind.Arith.CommRing
