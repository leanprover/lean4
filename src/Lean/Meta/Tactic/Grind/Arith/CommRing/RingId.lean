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

private def getAddFn (type : Expr) (u : Level) (semiringInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HAdd [u, u, u]) type type type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring addition{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``instHAdd [u]) type <| mkApp2 (mkConst ``Grind.Semiring.toAdd [u]) type semiringInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for addition{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type inst

private def getMulFn (type : Expr) (u : Level) (semiringInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HMul [u, u, u]) type type type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring multiplication{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``instHMul [u]) type <| mkApp2 (mkConst ``Grind.Semiring.toMul [u]) type semiringInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for multiplication{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HMul.hMul [u, u, u]) type type type inst

private def getSubFn (type : Expr) (u : Level) (ringInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HSub [u, u, u]) type type type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring subtraction{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``instHSub [u]) type <| mkApp2 (mkConst ``Grind.Ring.toSub [u]) type ringInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for subtraction{indentExpr inst}\nis not definitionally equal to the `Grind.Ring` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HSub.hSub [u, u, u]) type type type inst

private def getNegFn (type : Expr) (u : Level) (ringInst : Expr) : GoalM Expr := do
  let instType := mkApp (mkConst ``Neg [u]) type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring negation{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``Grind.Ring.toNeg [u]) type ringInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for negation{indentExpr inst}\nis not definitionally equal to the `Grind.Ring` one{indentExpr inst'}"
  internalizeFn <| mkApp2 (mkConst ``Neg.neg [u]) type inst

private def getPowFn (type : Expr) (u : Level) (semiringInst : Expr) : GoalM Expr := do
  let instType := mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type
  let .some inst ← trySynthInstance instType |
    throwError "failed to find instance for ring power operator{indentExpr instType}"
  let inst' := mkApp2 (mkConst ``Grind.Semiring.toHPow [u]) type semiringInst
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for power operator{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"
  internalizeFn <| mkApp4 (mkConst ``HPow.hPow [u, 0, u]) type Nat.mkType type inst

private def getIntCastFn (type : Expr) (u : Level) (ringInst : Expr) : GoalM Expr := do
  let inst' := mkApp2 (mkConst ``Grind.Ring.intCast [u]) type ringInst
  let instType := mkApp (mkConst ``IntCast [u]) type
  let inst := (← trySynthInstance instType).toOption.getD inst'
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for intCast{indentExpr inst}\nis not definitionally equal to the `Grind.Ring` one{indentExpr inst'}"
  internalizeFn <| mkApp2 (mkConst ``IntCast.intCast [u]) type inst

private def getNatCastFn (type : Expr) (u : Level) (semiringInst : Expr) : GoalM Expr := do
  let inst' := mkApp2 (mkConst ``Grind.Semiring.natCast [u]) type semiringInst
  let instType := mkApp (mkConst ``NatCast [u]) type
  let inst := (← trySynthInstance instType).toOption.getD inst'
  unless (← withDefault <| isDefEq inst inst') do
    throwError "instance for natCast{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"
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
    let semiring := mkApp (mkConst ``Grind.Semiring [u]) type
    let .some semiringInst ← trySynthInstance semiring | return none
    let ring := mkApp (mkConst ``Grind.Ring [u]) type
    let .some ringInst ← trySynthInstance ring | return none
    let commSemiring := mkApp (mkConst ``Grind.CommSemiring [u]) type
    let .some commSemiringInst ← trySynthInstance commSemiring | return none
    let commRing := mkApp (mkConst ``Grind.CommRing [u]) type
    let .some commRingInst ← trySynthInstance commRing | return none
    trace_goal[grind.ring] "new ring: {type}"
    let charInst? ← withNewMCtxDepth do
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let charType := mkApp3 (mkConst ``Grind.IsCharP [u]) type ringInst n
      let .some charInst ← trySynthInstance charType | pure none
      let n ← instantiateMVars n
      let some n ← evalNat n |>.run
        | trace_goal[grind.ring] "found instance for{indentExpr charType}\nbut characteristic is not a natural number"; pure none
      trace_goal[grind.ring] "characteristic: {n}"
      pure <| some (charInst, n)
    let noZeroDivInst? ← withNewMCtxDepth do
      let zeroType := mkApp (mkConst ``Zero [u]) type
      let .some zeroInst ← trySynthInstance zeroType | return none
      let hmulType := mkApp3 (mkConst ``HMul [0, u, u]) (mkConst ``Nat []) type type
      let .some hmulInst ← trySynthInstance hmulType | return none
      let noZeroDivType := mkApp3 (mkConst ``Grind.NoNatZeroDivisors [u]) type zeroInst hmulInst
      LOption.toOption <$> trySynthInstance noZeroDivType
    trace_goal[grind.ring] "NoNatZeroDivisors available: {noZeroDivInst?.isSome}"
    let addFn ← getAddFn type u semiringInst
    let mulFn ← getMulFn type u semiringInst
    let subFn ← getSubFn type u ringInst
    let negFn ← getNegFn type u ringInst
    let powFn ← getPowFn type u semiringInst
    let intCastFn ← getIntCastFn type u ringInst
    let natCastFn ← getNatCastFn type u semiringInst
    let id := (← get').rings.size
    let ring : Ring := { id, type, u, semiringInst, ringInst, commSemiringInst, commRingInst, charInst?, noZeroDivInst?, addFn, mulFn, subFn, negFn, powFn, intCastFn, natCastFn }
    modify' fun s => { s with rings := s.rings.push ring }
    return some id

end Lean.Meta.Grind.Arith.CommRing
