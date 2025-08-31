/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.MBTC
public import Lean.Meta.Tactic.Grind.Arith.Linear.Model
public import Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq

public section

namespace Lean.Meta.Grind.Arith.Linear

private partial def toRatValue? (a : Expr) : Option Rat :=
  if a.isAppOfArity ``Zero.zero 2 then
    some 0
  else if a.isAppOfArity ``One.one 2 then
    some 1
  else if a.isAppOfArity ``OfNat.ofNat 3 then
    toRatValue? (a.getArg! 1)
  else if a.isAppOfArity ``Neg.neg 3 then
    (- ·) <$> toRatValue? a.appArg!
  else if a.isAppOfArity ``HDiv.hDiv 6 then
    (· / ·) <$> toRatValue? a.appFn!.appArg! <*> toRatValue? a.appArg!
  else if let .lit (.natVal n) := a then
    some (mkRat n 1)
  else
    none

private def getAssignmentExt? (s : Struct) (a : Expr) : Option Rat := do
  if let some v := getAssignment? s a then
    some v
  else
    toRatValue? a

private def hasTheoryVar (e : Expr) : GoalM Bool := do
  return (← getRootENode e).linarith?.isSome || (toRatValue? e).isSome

private def isInterpreted (e : Expr) : GoalM Bool := do
  if isInterpretedTerm e then return true
  let f := e.getAppFn
  return f.isConstOf ``LE.le || f.isConstOf ``LT.lt || f.isConstOf ``Dvd.dvd

private def eqAssignment (a b : Expr) : GoalM Bool := do
  let structId₁? := (← get).arith.linear.exprToStructId.find? { expr := a }
  let structId₂? := (← get).arith.linear.exprToStructId.find? { expr := b }
  let some structId := structId₁? <|> structId₂? | return false
  let s := (← get).arith.linear.structs[structId]!
  -- It is pointless to generate case-splits unless we have support for disequality.
  unless s.isLinearInst?.isSome do return false
  let some v₁ := getAssignmentExt? s a | return false
  let some v₂ := getAssignmentExt? s b | return false
  return v₁ == v₂

def mbtc : GoalM Bool := do
  Grind.mbtc {
    hasTheoryVar := hasTheoryVar
    isInterpreted := isInterpreted
    eqAssignment := eqAssignment
  }

end Lean.Meta.Grind.Arith.Linear
