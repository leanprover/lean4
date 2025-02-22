/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var

namespace Int.Linear
/-- Returns `true` if all coefficients are not `0`. -/
def Poly.checkCoeffs : Poly → Bool
  | .num _ => true
  | .add k _ p => k != 0 && checkCoeffs p

end Int.Linear

namespace Lean.Meta.Grind.Arith.Cutsat

def checkRelCnstrs (css : PArray (PArray RelCnstrWithProof)) (isLower : Bool) : GoalM Unit := do
  let mut x := 0
  for cs in css do
    for { c, .. } in cs do
      assert! c.isLe
      assert! c.isSorted
      assert! c.p.checkCoeffs
      let .add a y _ := c.p | unreachable!
      assert! isLower == (a < 0)
      assert! x == y
    x := x + 1
  return ()

def checkLowers : GoalM Unit := do
  let s ← get'
  assert! s.lowers.size == s.vars.size
  checkRelCnstrs s.lowers (isLower := true)

def checkUppers : GoalM Unit := do
  let s ← get'
  assert! s.uppers.size == s.vars.size
  checkRelCnstrs s.uppers (isLower := false)

def checkDvdCnstrs : GoalM Unit := do
  let s ← get'
  assert! s.vars.size == s.dvdCnstrs.size
  let mut x := 0
  for c? in s.dvdCnstrs do
    if let some { c, .. } := c? then
      assert! c.p.checkCoeffs
      assert! c.p.isSorted
      assert! c.k > 1
      let .add _ y _ := c.p | unreachable!
      assert! x == y
    x := x + 1

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
  checkLowers
  checkUppers

end Lean.Meta.Grind.Arith.Cutsat
