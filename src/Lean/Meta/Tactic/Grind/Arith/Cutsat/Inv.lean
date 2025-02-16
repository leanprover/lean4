/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

def checkDvdCnstrs : GoalM Unit := do
  let s ← get'
  assert! s.vars.size == s.dvdCnstrs.size
  -- TODO: condition maximal variable

def checkVars : GoalM Unit := do
  let s ← get'
  let mut num := 0
  for ({ expr }, var) in s.varMap do
    if h : var < s.vars.size then
      let expr' := s.vars[var]
      assert! isSameExpr expr expr'
    else
      unreachable!
    num := num + 1
  assert! s.vars.size == num

def checkInvariants : GoalM Unit := do
  checkVars
  checkDvdCnstrs

end Lean.Meta.Grind.Arith.Cutsat
