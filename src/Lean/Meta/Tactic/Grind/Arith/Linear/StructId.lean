/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Ordered.Module
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.Var

namespace Lean.Meta.Grind.Arith.Linear

private def internalizeFn (fn : Expr) : GoalM Expr := do
  shareCommon (← canon fn)

open Grind.Linarith (Poly)

def getStructId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let getInst? (declName : Name) : GoalM (Option Expr) := do
      let instType := mkApp (mkConst declName [u]) type
      return LOption.toOption (← trySynthInstance instType)
    let getInst (declName : Name) : GoalM Expr := do
      let instType := mkApp (mkConst declName [u]) type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let getBinHomoInst (declName : Name) : GoalM Expr := do
      let instType := mkApp3 (mkConst declName [u, u, u]) type type type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let getHMulInst : GoalM Expr := do
      let instType := mkApp3 (mkConst ``HMul [0, u, u]) Int.mkType type type
      let .some inst ← trySynthInstance instType
        | throwError "`grind linarith` failed to find instance{indentExpr instType}"
      return inst
    let checkToFieldDefEq? (parentInst? : Option Expr) (inst? : Option Expr) (toFieldName : Name) : GoalM (Option Expr) := do
      let some parentInst := parentInst? | return none
      let some inst := inst? | return none
      let toField := mkApp2 (mkConst toFieldName [u]) type inst
      unless (← isDefEq parentInst toField) do
        reportIssue! "`grind linarith` expected{indentExpr parentInst}\nto be definitionally equal to{indentExpr toField}"
        return none
      return some inst
    let ensureToFieldDefEq (parentInst : Expr) (inst : Expr) (toFieldName : Name) : GoalM Unit := do
      let toField := mkApp2 (mkConst toFieldName [u]) type inst
      unless (← isDefEq parentInst toField) do
        throwError "`grind linarith` expected{indentExpr parentInst}\nto be definitionally equal to{indentExpr toField}"
    let some intModuleInst ← getInst? ``Grind.IntModule | return none
    let zeroInst ← getInst ``Zero
    let zero := mkApp2 (mkConst ``Zero.zero [u]) type zeroInst
    let addInst ← getBinHomoInst ``HAdd
    let addFn := mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type addInst
    let subInst ← getBinHomoInst ``HSub
    let subFn := mkApp4 (mkConst ``HSub.hSub [u, u, u]) type type type subInst
    let negInst ← getInst ``Neg
    let negFn := mkApp2 (mkConst ``Neg.neg [u]) type negInst
    let hmulInst ← getHMulInst
    let hmulFn := mkApp4 (mkConst ``HMul.hMul [0, u, u]) Int.mkType type type hmulInst
    ensureToFieldDefEq zeroInst intModuleInst ``Grind.IntModule.toZero
    ensureToFieldDefEq addInst intModuleInst ``Grind.IntModule.toAdd
    ensureToFieldDefEq subInst intModuleInst ``Grind.IntModule.toSub
    ensureToFieldDefEq negInst intModuleInst ``Grind.IntModule.toNeg
    ensureToFieldDefEq hmulInst intModuleInst ``Grind.IntModule.toHMul
    let some preorderInst ← getInst? ``Grind.Preorder | return none
    let leInst ← getInst ``LE
    let ltInst ← getInst ``LT
    let leFn := mkApp2 (mkConst ``LE.le [u]) type leInst
    let ltFn := mkApp2 (mkConst ``LT.lt [u]) type ltInst
    ensureToFieldDefEq leInst preorderInst ``Grind.Preorder.toLE
    ensureToFieldDefEq ltInst preorderInst ``Grind.Preorder.toLT
    let partialInst? ← checkToFieldDefEq? (some preorderInst) (← getInst? ``Grind.PartialOrder) ``Grind.PartialOrder.toPreorder
    let linearInst? ← checkToFieldDefEq? partialInst? (← getInst? ``Grind.LinearOrder) ``Grind.LinearOrder.toPartialOrder
    let isOrderedType := mkApp3 (mkConst ``Grind.IntModule.IsOrdered [u]) type preorderInst intModuleInst
    let .some isOrdInst ← trySynthInstance isOrderedType | return none
    let getSMulFn? : GoalM (Option Expr) := do
      let smulType := mkApp2 (mkConst ``SMul [0, u]) Int.mkType type
      let .some smulInst ← trySynthInstance smulType | return none
      let smulFn := mkApp3 (mkConst ``SMul.smul [0, u]) Int.mkType type smulInst
      if (← isDefEq hmulFn smulFn) then
        return smulFn
      reportIssue! "`grind linarith` expected{indentExpr hmulFn}\nto be definitionally equal to{indentExpr smulFn}"
      return none
    let smulFn? ← getSMulFn?
    let ringInst? ← getInst? ``Grind.Ring
    let getOne? : GoalM (Option Expr) := do
      let some oneInst ← getInst? ``One | return none
      let one := mkApp2 (mkConst ``One.one [u]) type oneInst
      let one' ← mkNumeral type 1
      unless (← isDefEq one one') do reportIssue! "`grind linarith` expected{indentExpr one}\nto be definitionally equal to{indentExpr one'}"
      return some one
    let one? ← getOne?
    let commRingInst? ← getInst? ``Grind.CommRing
    let getRingIsOrdInst? : GoalM (Option Expr) := do
      let some ringInst := ringInst? | return none
      let isOrdType := mkApp3 (mkConst ``Grind.Ring.IsOrdered [u]) type ringInst preorderInst
      return LOption.toOption (← trySynthInstance isOrdType)
    let ringIsOrdInst? ← getRingIsOrdInst?
    let getNoNatZeroDivInst? : GoalM (Option Expr) := do
      let hmulNat := mkApp3 (mkConst ``HMul [0, u, u]) Nat.mkType type type
      let .some hmulInst ← trySynthInstance hmulNat | return none
      let noNatZeroDivType := mkApp3 (mkConst ``Grind.NoNatZeroDivisors [u]) type zeroInst hmulInst
      return LOption.toOption (← trySynthInstance noNatZeroDivType)
    let noNatDivInst? ← getNoNatZeroDivInst?
    let id := (← get').structs.size
    let struct : Struct := {
      id, type, u, intModuleInst, preorderInst, isOrdInst, partialInst?, linearInst?, noNatDivInst?
      leFn, ltFn, addFn, subFn, negFn, hmulFn, smulFn?, zero, one?
      ringInst?, commRingInst?, ringIsOrdInst?
    }
    modify' fun s => { s with structs := s.structs.push struct }
    if let some one := one? then
      if ringInst?.isSome then LinearM.run id do
        -- Create `1` variable, and assert strict lower bound `0 < 1`
        let x ← mkVar one
        let p := Poly.add (-1) x .nil
        modifyStruct fun s => { s with
          lowers := s.lowers.modify x fun cs => cs.push { p, h := .oneGtZero, strict := true }
        }
    return some id

end Lean.Meta.Grind.Arith.Linear
