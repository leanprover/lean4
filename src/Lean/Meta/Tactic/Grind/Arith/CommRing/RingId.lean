/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util

namespace Lean.Meta.Grind.Arith.CommRing

private def internalizeFn (fn : Expr) : GoalM Expr := do
  shareCommon (← canon fn)

private def getAddFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HAdd [u, u, u]) type type type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring addition{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``instHAdd [u]) type <| mkApp2 (mkConst ``Grind.CommRing.toAdd [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for addition{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type inst

private def getMulFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HMul [u, u, u]) type type type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring multiplication{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``instHMul [u]) type <| mkApp2 (mkConst ``Grind.CommRing.toMul [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for multiplication{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HMul.hMul [u, u, u]) type type type inst

private def getSubFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HSub [u, u, u]) type type type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring subtraction{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``instHSub [u]) type <| mkApp2 (mkConst ``Grind.CommRing.toSub [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for subtraction{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HSub.hSub [u, u, u]) type type type inst

private def getNegFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp (mkConst ``Neg [u]) type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring negation{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``Grind.CommRing.toNeg [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for negation{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp2 (mkConst ``Neg.neg [u]) type inst

private def getPowFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring power operator{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``Grind.CommRing.toHPow [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for power operator{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HPow.hPow [u, 0, u]) type Nat.mkType type inst

private def getIntCastFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp (mkConst ``IntCast [u]) type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring intCast{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``Grind.CommRing.intCast [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for intCast{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp2 (mkConst ``IntCast.intCast [u]) type inst

private def getNatCastFn (type : Expr) (u : Level) (commRingInst : Expr) : GoalM Expr := do
  let instType := mkApp (mkConst ``NatCast [u]) type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring natCast{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``Grind.CommRing.natCastInst [u]) type commRingInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for natCast{indentExpr inst}\nis not definitionally equal to the `Grind.CommRing` one{indentExpr inst'}"
  internalizeFn <| mkApp2 (mkConst ``NatCast.natCast [u]) type inst

/--
Returns the ring id for the given type if there is a `CommRing` instance for it.

This function will also perform sanity-checks
(e.g., the `Add` instance for `type` must be definitionally equal to the `CommRing.toAdd` one.)

It also caches the functions representing `+`, `*`, `-`, `^`, and `intCast`.
-/
def getRingId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let ring := mkApp (mkConst ``Grind.CommRing [u]) type
    let .some commRingInst ← trySynthInstance ring | return none
    trace_goal[grind.ring] "new ring: {type}"
    let charInst? ← withNewMCtxDepth do
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let charType := mkApp3 (mkConst ``Grind.IsCharP [u]) type commRingInst n
      let .some charInst ← trySynthInstance charType | pure none
      let n ← instantiateMVars n
      let some n ← evalNat n |>.run
        | trace_goal[grind.ring] "found instance for{indentExpr charType}\nbut characteristic is not a natural number"; pure none
      trace_goal[grind.ring] "characteristic: {n}"
      pure <| some (charInst, n)
    let noZeroDivType := mkApp2 (mkConst ``Grind.NoZeroNatDivisors [u]) type commRingInst
    let noZeroDivInst? := (← trySynthInstance noZeroDivType).toOption
    trace_goal[grind.ring] "NoZeroNatDivisors available: {noZeroDivInst?.isSome}"
    let addFn ← getAddFn type u commRingInst
    let mulFn ← getMulFn type u commRingInst
    let subFn ← getSubFn type u commRingInst
    let negFn ← getNegFn type u commRingInst
    let powFn ← getPowFn type u commRingInst
    let intCastFn ← getIntCastFn type u commRingInst
    let natCastFn ← getNatCastFn type u commRingInst
    let id := (← get').rings.size
    let ring : Ring := { id, type, u, commRingInst, charInst?, noZeroDivInst?, addFn, mulFn, subFn, negFn, powFn, intCastFn, natCastFn }
    modify' fun s => { s with rings := s.rings.push ring }
    return some id

end Lean.Meta.Grind.Arith.CommRing
