/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

namespace Lean.Meta.Grind.Arith.CommRing

private def checkVars : RingM Unit := do
  let s ← getRing
  let mut num := 0
  for ({ expr }, var) in s.varMap do
    if h : var < s.vars.size then
      let expr' := s.vars[var]
      assert! isSameExpr expr expr'
    else
      unreachable!
    num := num + 1
  assert! s.vars.size == num

private def checkPoly (p : Poly) : RingM Unit := do
  assert! p.isSorted
  assert! p.checkCoeffs
  assert! p.checkNoUnitMon
  assert! !(p matches .num _)

private def checkBasis : RingM Unit := do
  let mut x := 0
  for cs in (← getRing).varToBasis do
    for c in cs do
      checkPoly c.p
      let .add _ m _ := c.p | unreachable!
      let .mult pw _ := m | unreachable!
      assert! pw.x == x
    x := x + 1

private def checkQueue : RingM Unit := do
  for c in (← getRing).queue do
    checkPoly c.p

private def checkDiseqs : RingM Unit := do
  for c in (← getRing).diseqs do
    checkPoly c.d.p

private def checkRingInvs : RingM Unit := do
  checkVars
  checkBasis
  checkQueue
  checkDiseqs

def checkInvariants : GoalM Unit := do
  unless grind.debug.get (← getOptions) do return ()
  for ringId in [: (← get').rings.size] do
    RingM.run ringId do
      assert! (← getRingId) == ringId
      checkRingInvs

end Lean.Meta.Grind.Arith.CommRing
