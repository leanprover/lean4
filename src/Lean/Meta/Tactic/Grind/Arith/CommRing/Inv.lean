/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
public section
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
  for c in (← getCommRing).basis do
    checkPoly c.p
    x := x + 1

private def checkQueue : RingM Unit := do
  for c in (← getCommRing).queue do
    checkPoly c.p

private def checkDiseqs : RingM Unit := do
  for c in (← getCommRing).diseqs do
    checkPoly c.d.p

private def checkRingInvs : RingM Unit := do
  checkVars
  checkBasis
  checkQueue
  checkDiseqs

def checkInvariants : GoalM Unit := do
  if (← isDebugEnabled) then
  for ringId in *...(← get').rings.size do
    RingM.run ringId do
      assert! (← getRingId) == ringId
      checkRingInvs

end Lean.Meta.Grind.Arith.CommRing
