/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Ordered.Module
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.Var

namespace Lean.Meta.Grind.Arith.Linear

private def preprocess (e : Expr) : GoalM Expr := do
  shareCommon (← canon e)

private def internalizeFn (fn : Expr) : GoalM Expr := do
  preprocess fn

private def preprocessConst (c : Expr) : GoalM Expr := do
  let c ← preprocess c
  internalize c 0 none
  return c

private def internalizeConst (c : Expr) : GoalM Expr := do
  let c ← shareCommon (← canon c)
  internalize c 0 none
  return c

open Grind.Linarith (Poly)

private def mkExpectedDefEqMsg (a b : Expr) : MetaM MessageData :=
  return m!"`grind linarith` expected{indentExpr a}\nto be definitionally equal to{indentExpr b}"

private def ensureDefEq (a b : Expr) : MetaM Unit := do
  unless (← withDefault <| isDefEq a b) do
    throwError (← mkExpectedDefEqMsg a b)

private def addZeroLtOne (one : Var) : LinearM Unit := do
  let p := Poly.add (-1) one .nil
  modifyStruct fun s => { s with
    lowers := s.lowers.modify one fun cs => cs.push { p, h := .oneGtZero, strict := true }
  }

private def addZeroNeOne (one : Var) : LinearM Unit := do
  let p := Poly.add 1 one .nil
  modifyStruct fun s => { s with
    diseqs := s.diseqs.modify one fun cs => cs.push { p, h := .oneNeZero }
  }

private def isNonTrivialIsCharInst (isCharInst? : Option (Expr × Nat)) : Bool :=
  match isCharInst? with
  | some (_, c) => c != 1
  | none => false

def getStructId? (type : Expr) : GoalM (Option Nat) := do
  unless (← getConfig).linarith do return none
  if (← getConfig).cutsat && Cutsat.isSupportedType type then
    -- If `type` is supported by cutsat, let it handle
    return none
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let rec getInst? (declName : Name) : GoalM (Option Expr) := do
      let instType := mkApp (mkConst declName [u]) type
      return LOption.toOption (← trySynthInstance instType)
    let rec getInst (declName : Name) : GoalM Expr := do
      let instType := mkApp (mkConst declName [u]) type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let rec getBinHomoInst (declName : Name) : GoalM Expr := do
      let instType := mkApp3 (mkConst declName [u, u, u]) type type type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let rec getHMulInst : GoalM Expr := do
      let instType := mkApp3 (mkConst ``HMul [0, u, u]) Int.mkType type type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let rec getHMulNatInst : GoalM Expr := do
      let instType := mkApp3 (mkConst ``HMul [0, u, u]) Nat.mkType type type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let rec checkToFieldDefEq? (parentInst? : Option Expr) (inst? : Option Expr) (toFieldName : Name) : GoalM (Option Expr) := do
      let some parentInst := parentInst? | return none
      let some inst := inst? | return none
      let toField := mkApp2 (mkConst toFieldName [u]) type inst
      unless (← withDefault <| isDefEq parentInst toField) do
        reportIssue! (← mkExpectedDefEqMsg parentInst toField)
        return none
      return some inst
    let rec ensureToFieldDefEq (parentInst : Expr) (inst : Expr) (toFieldName : Name) : GoalM Unit := do
      let toField := mkApp2 (mkConst toFieldName [u]) type inst
      ensureDefEq parentInst toField
    let rec ensureToHomoFieldDefEq (parentInst : Expr) (inst : Expr) (toFieldName : Name) (toHeteroName : Name) : GoalM Unit := do
      let toField := mkApp2 (mkConst toFieldName [u]) type inst
      let heteroToField := mkApp2 (mkConst toHeteroName [u]) type toField
      ensureDefEq parentInst heteroToField
    let some intModuleInst ← getInst? ``Grind.IntModule | return none
    let zeroInst ← getInst ``Zero
    let zero ← internalizeConst <| mkApp2 (mkConst ``Zero.zero [u]) type zeroInst
    let ofNatZeroType := mkApp2 (mkConst ``OfNat [u]) type (mkRawNatLit 0)
    let some ofNatZeroInst := LOption.toOption (← trySynthInstance ofNatZeroType) | return none
    -- `ofNatZero` is used internally, we don't need to internalize
    let ofNatZero ← preprocess <| mkApp3 (mkConst ``OfNat.ofNat [u]) type (mkRawNatLit 0) ofNatZeroInst
    ensureDefEq zero ofNatZero
    let addInst ← getBinHomoInst ``HAdd
    let addFn ← internalizeFn <| mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type addInst
    let subInst ← getBinHomoInst ``HSub
    let subFn ← internalizeFn <| mkApp4 (mkConst ``HSub.hSub [u, u, u]) type type type subInst
    let negInst ← getInst ``Neg
    let negFn ← internalizeFn <| mkApp2 (mkConst ``Neg.neg [u]) type negInst
    let hmulInst ← getHMulInst
    let hmulFn ← internalizeFn <| mkApp4 (mkConst ``HMul.hMul [0, u, u]) Int.mkType type type hmulInst
    let hmulNatInst ← getHMulNatInst
    let hmulNatFn ← internalizeFn <| mkApp4 (mkConst ``HMul.hMul [0, u, u]) Nat.mkType type type hmulNatInst
    ensureToFieldDefEq zeroInst intModuleInst ``Grind.IntModule.toZero
    ensureToHomoFieldDefEq addInst intModuleInst ``Grind.IntModule.toAdd ``instHAdd
    ensureToHomoFieldDefEq subInst intModuleInst ``Grind.IntModule.toSub ``instHSub
    ensureToFieldDefEq negInst intModuleInst ``Grind.IntModule.toNeg
    ensureToFieldDefEq hmulInst intModuleInst ``Grind.IntModule.toHMul
    let preorderInst? ← getInst? ``Grind.Preorder
    let isOrdInst? ← if let some preorderInst := preorderInst? then
      let isOrderedType := mkApp3 (mkConst ``Grind.IntModule.IsOrdered [u]) type preorderInst intModuleInst
      pure <| LOption.toOption (← trySynthInstance isOrderedType)
    else
      pure none
    let preorderInst? := if isOrdInst?.isNone then none else preorderInst?
    let partialInst? ← checkToFieldDefEq? preorderInst? (← getInst? ``Grind.PartialOrder) ``Grind.PartialOrder.toPreorder
    let linearInst? ← checkToFieldDefEq? partialInst? (← getInst? ``Grind.LinearOrder) ``Grind.LinearOrder.toPartialOrder
    let (leFn?, ltFn?) ← if let some preorderInst := preorderInst? then
      let leInst ← getInst ``LE
      let ltInst ← getInst ``LT
      let leFn ← internalizeFn <| mkApp2 (mkConst ``LE.le [u]) type leInst
      let ltFn ← internalizeFn <| mkApp2 (mkConst ``LT.lt [u]) type ltInst
      ensureToFieldDefEq leInst preorderInst ``Grind.Preorder.toLE
      ensureToFieldDefEq ltInst preorderInst ``Grind.Preorder.toLT
      pure (some leFn, some ltFn)
    else
      pure (none, none)
    let getHSMulFn? : GoalM (Option Expr) := do
      let smulType := mkApp3 (mkConst ``HSMul [0, u, u]) Int.mkType type type
      let .some smulInst ← trySynthInstance smulType | return none
      internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Int.mkType type smulInst smulInst
    let getHSMulNatFn? : GoalM (Option Expr) := do
      let smulType := mkApp3 (mkConst ``HSMul [0, u, u]) Nat.mkType type type
      let .some smulInst ← trySynthInstance smulType | return none
      internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Nat.mkType type smulInst smulInst
    let hsmulFn? ← getHSMulFn?
    let hsmulNatFn? ← getHSMulNatFn?
    let ringId? ← CommRing.getRingId? type
    let ringInst? ← getInst? ``Grind.Ring
    let fieldInst? ← getInst? ``Grind.Field
    let getOne? : GoalM (Option Expr) := do
      let some oneInst ← getInst? ``One | return none
      let one ← internalizeConst <| mkApp2 (mkConst ``One.one [u]) type oneInst
      let one' ← mkNumeral type 1
      unless (← withDefault <| isDefEq one one') do reportIssue! (← mkExpectedDefEqMsg one one')
      return some one
    let one? ← getOne?
    let commRingInst? ← getInst? ``Grind.CommRing
    let getRingIsOrdInst? : GoalM (Option Expr) := do
      let some ringInst := ringInst? | return none
      let some preorderInst := preorderInst? | return none
      let isOrdType := mkApp3 (mkConst ``Grind.Ring.IsOrdered [u]) type ringInst preorderInst
      let .some inst ← trySynthInstance isOrdType
        | reportIssue! "type is an ordered `IntModule` and a `Ring`, but is not an ordered ring, failed to synthesize{indentExpr isOrdType}"
          return none
      return some inst
    let ringIsOrdInst? ← getRingIsOrdInst?
    let charInst? ← if let some ringInst := ringInst? then getIsCharInst? u type ringInst else pure none
    let getNoNatZeroDivInst? : GoalM (Option Expr) := do
      let hmulNat := mkApp3 (mkConst ``HMul [0, u, u]) Nat.mkType type type
      let .some hmulInst ← trySynthInstance hmulNat | return none
      let noNatZeroDivType := mkApp3 (mkConst ``Grind.NoNatZeroDivisors [u]) type zeroInst hmulInst
      return LOption.toOption (← trySynthInstance noNatZeroDivType)
    let noNatDivInst? ← getNoNatZeroDivInst?
    let id := (← get').structs.size
    let struct : Struct := {
      id, type, u, intModuleInst, preorderInst?, isOrdInst?, partialInst?, linearInst?, noNatDivInst?
      leFn?, ltFn?, addFn, subFn, negFn, hmulFn, hmulNatFn, hsmulFn?, hsmulNatFn?, zero, one?
      ringInst?, commRingInst?, ringIsOrdInst?, charInst?, ringId?, fieldInst?, ofNatZero
    }
    modify' fun s => { s with structs := s.structs.push struct }
    if let some one := one? then
      if ringInst?.isSome then LinearM.run id do
        if ringIsOrdInst?.isSome then
          -- Create `1` variable, and assert strict lower bound `0 < 1` and `0 ≠ 1`
          let x ← mkVar one (mark := false)
          addZeroLtOne x
          addZeroNeOne x
        else if fieldInst?.isSome || isNonTrivialIsCharInst charInst? then
          -- Create `1` variable, and assert `0 ≠ 1`
          let x ← mkVar one (mark := false)
          addZeroNeOne x

    return some id

end Lean.Meta.Grind.Arith.Linear
