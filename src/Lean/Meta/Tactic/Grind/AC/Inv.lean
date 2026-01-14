/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.Tactic.Grind.AC.Seq
namespace Lean.Meta.Grind.AC
open Lean.Grind

def checkVars : ACM Unit := do
  let s ← getStruct
  let mut num := 0
  for ({ expr }, var) in s.varMap do
    if h : var < s.vars.size then
      let expr' := s.vars[var]
      assert! isSameExpr expr expr'
    else
      unreachable!
    num := num + 1
  assert! s.vars.size == num

def checkSeq (s : AC.Seq) : ACM Unit := do
  if (← isCommutative) then
    assert! s.isSorted
  if (← hasNeutral) then
    assert! !s.contains 0 || s == .var 0
  if (← isIdempotent) then
    assert! s.noAdjacentDuplicates

def checkLhsRhs (lhs rhs : AC.Seq) : ACM Unit := do
  checkSeq lhs; checkSeq rhs

def checkBasis : ACM Unit := do
  for c in (← getStruct).basis do
    assert! compare c.lhs c.rhs == .gt
    checkLhsRhs c.lhs c.rhs

def checkQueue : ACM Unit := do
  for c in (← getStruct).queue do
    checkLhsRhs c.lhs c.rhs

def checkDiseqs : ACM Unit := do
  for c in (← getStruct).diseqs do
    checkLhsRhs c.lhs c.rhs

def checkStructInvs : ACM Unit := do
  checkVars
  checkBasis
  checkQueue
  checkDiseqs

public def checkInvariants : GoalM Unit := do
  if (← isDebugEnabled) then
  for opId in *...(← get').structs.size do
    ACM.run opId checkStructInvs

end Lean.Meta.Grind.AC
