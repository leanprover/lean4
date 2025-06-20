/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Ring.Field
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util

namespace Lean.Meta.Grind.Arith.CommRing

def denoteNumCore (u : Level) (type : Expr) (semiringInst : Expr) (negFn : Expr) (k : Int) : Expr :=
  let n := mkRawNatLit k.natAbs
  let ofNatInst := mkApp3 (mkConst ``Grind.Semiring.ofNat [u]) type semiringInst n
  let n := mkApp3 (mkConst ``OfNat.ofNat [u]) type n ofNatInst
  if k < 0 then
    mkApp negFn n
  else
    n

private def internalizeFn (fn : Expr) : GoalM Expr := do
  shareCommon (← canon fn)

private def getUnaryFn (type : Expr)(u : Level) (instDeclName : Name) (declName : Name) : GoalM Expr := do
  let instType := mkApp (mkConst instDeclName [u]) type
  let .some inst ← trySynthInstance instType
    | throwError "`grind ring` failed to find instance{indentExpr instType}"
  internalizeFn <| mkApp2 (mkConst declName [u]) type inst

private def getBinHomoFn (type : Expr)(u : Level) (instDeclName : Name) (declName : Name) : GoalM Expr := do
  let instType := mkApp3 (mkConst instDeclName [u, u, u]) type type type
  let .some inst ← trySynthInstance instType
    | throwError "`grind ring` failed to find instance{indentExpr instType}"
  internalizeFn <| mkApp4 (mkConst declName [u, u, u]) type type type inst

-- Remark: we removed consistency checks such as the one that ensures `HAdd` instance matches `Semiring.toAdd`
-- That is, we are assuming the type classes were properly setup.

private def getAddFn (type : Expr) (u : Level) : GoalM Expr := do
  getBinHomoFn type u ``HAdd ``HAdd.hAdd

private def getMulFn (type : Expr) (u : Level) : GoalM Expr := do
  getBinHomoFn type u ``HMul ``HMul.hMul

private def getSubFn (type : Expr) (u : Level) : GoalM Expr := do
  getBinHomoFn type u ``HSub ``HSub.hSub

private def getDivFn (type : Expr) (u : Level) : GoalM Expr := do
  getBinHomoFn type u ``HDiv ``HDiv.hDiv

private def getNegFn (type : Expr) (u : Level) : GoalM Expr := do
  getUnaryFn type u ``Neg ``Neg.neg

private def getInvFn (type : Expr) (u : Level) : GoalM Expr := do
  getUnaryFn type u ``Inv ``Inv.inv

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
  -- Note that `Ring.intCast` is not registered as a global instance
  -- (to avoid introducing unwanted coercions)
  -- so merely having a `Ring α` instance
  -- does not guarantee that an `IntCast α` will be available.
  -- When both are present we verify that they are defeq,
  -- and otherwise fall back to the field of the `Ring α` instance that we already have.
  let inst ← match (← trySynthInstance instType).toOption with
  | none => pure inst'
  | some inst =>
    unless (← withDefault <| isDefEq inst inst') do
      throwError "instance for intCast{indentExpr inst}\nis not definitionally equal to the `Grind.Ring` one{indentExpr inst'}"
    pure inst
  internalizeFn <| mkApp2 (mkConst ``IntCast.intCast [u]) type inst

private def getNatCastFn (type : Expr) (u : Level) (semiringInst : Expr) : GoalM Expr := do
  let inst' := mkApp2 (mkConst ``Grind.Semiring.natCast [u]) type semiringInst
  let instType := mkApp (mkConst ``NatCast [u]) type
  -- Note that `Semiring.natCast` is not registered as a global instance
  -- (to avoid introducing unwanted coercions)
  -- so merely having a `Semiring α` instance
  -- does not guarantee that an `NatCast α` will be available.
  -- When both are present we verify that they are defeq,
  -- and otherwise fall back to the field of the `Semiring α` instance that we already have.
  let inst ← match (← trySynthInstance instType).toOption with
  | none => pure inst'
  | some inst =>
    unless (← withDefault <| isDefEq inst inst') do
      throwError "instance for natCast{indentExpr inst}\nis not definitionally equal to the `Grind.Semiring` one{indentExpr inst'}"
    pure inst
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
    if let some id := id? then
      -- Internalize helper constants
      let ring := (← get').rings[id]!
      internalize ring.one 0
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
    let charInst? ← getIsCharInst? u type ringInst
    let noZeroDivInst? ← getNoZeroDivInst? u type
    trace_goal[grind.ring] "NoNatZeroDivisors available: {noZeroDivInst?.isSome}"
    let field := mkApp (mkConst ``Grind.Field [u]) type
    let fieldInst? : Option Expr ← LOption.toOption <$> trySynthInstance field
    let addFn ← getAddFn type u
    let mulFn ← getMulFn type u
    let subFn ← getSubFn type u
    let negFn ← getNegFn type u
    let powFn ← getPowFn type u semiringInst
    let intCastFn ← getIntCastFn type u ringInst
    let natCastFn ← getNatCastFn type u semiringInst
    let invFn? ← if fieldInst?.isSome then
      pure (some (← getInvFn type u))
    else
      pure none
    let one ← shareCommon <| (← canon <| denoteNumCore u type semiringInst negFn 1)
    let id := (← get').rings.size
    let ring : Ring := {
      id, type, u, semiringInst, ringInst, commSemiringInst, commRingInst, charInst?, noZeroDivInst?, fieldInst?,
      addFn, mulFn, subFn, negFn, powFn, intCastFn, natCastFn, invFn?, one }
    modify' fun s => { s with rings := s.rings.push ring }
    return some id

end Lean.Meta.Grind.Arith.CommRing
