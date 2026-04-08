/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.OrderInsts
import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Insts
import Init.Grind.Module.Envelope
public section
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
  unless (← isDefEqD a b) do
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

private def isCutsatType (type : Expr) : GoalM Bool := do
  if (← getConfig).lia then
    if (← Cutsat.isSupportedType type) then
      -- If `type` is supported by cutsat, let it handle
      return true
  return false

private def getCommRingInst? (ringId? : Option Nat) : GoalM (Option Expr) := do
  let some ringId := ringId? | return none
  return some (← CommRing.RingM.run ringId do return (← CommRing.getCommRing).commRingInst)

private def mkRingInst? (u : Level) (type : Expr) (commRingInst? : Option Expr) : GoalM (Option Expr) := do
  if let some commRingInst := commRingInst? then
    return mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
  else
    synthInstance? <| mkApp (mkConst ``Grind.Ring [u]) type

private def mkIntModuleInst? (u : Level) (type : Expr) (ringInst? : Option Expr) : GoalM (Option Expr) := do
  if let some ringInst := ringInst? then
    return some <| mkApp2 (mkConst ``Grind.Ring.toIntModule [u]) type ringInst
  else
    synthInstance? <| mkApp (mkConst ``Grind.IntModule [u]) type

private def mkSemiringInst? (u : Level) (type : Expr) (ringInst? : Option Expr) : GoalM (Option Expr) := do
  if let some ringInst := ringInst? then
    return some <| mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  else
    synthInstance? <| mkApp (mkConst ``Grind.Semiring [u]) type

private def mkOne? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let some oneInst ← synthInstance? (mkApp (mkConst ``One [u]) type) | return none
  let one ← internalizeConst <| mkApp2 (mkConst ``One.one [u]) type oneInst
  let one' ← mkNumeral type 1
  unless (← isDefEqD one one') do reportIssue! (← mkExpectedDefEqMsg one one')
  return some one

private def mkOrderedRingInst? (u : Level) (type : Expr) (semiringInst? leInst? ltInst? preorderInst? : Option Expr) : GoalM (Option Expr) := do
  let some semiringInst := semiringInst? | return none
  let some leInst := leInst? | return none
  let some ltInst := ltInst? | return none
  let some preorderInst := preorderInst? | return none
  let isOrdType := mkApp5 (mkConst ``Grind.OrderedRing [u]) type semiringInst leInst ltInst preorderInst
  let some inst ← synthInstance? isOrdType
    | -- TODO: this issue message should explain which behaviours are disabled when then ordered ring instance is not available.
      reportIssue! "type has a `Preorder` and is a `Semiring`, but is not an ordered ring, failed to synthesize{indentExpr isOrdType}"
      return none
  return some inst

private def mkNoNatZeroDivInst? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let natModuleType := mkApp (mkConst ``Grind.NatModule [u]) type
  let some natModuleInst ← synthInstance? natModuleType | return none
  synthInstance? <| mkApp2 (mkConst ``Grind.NoNatZeroDivisors [u]) type natModuleInst

private def getInst? (declName : Name) (u : Level) (type : Expr) : GoalM (Option Expr) := do
  synthInstance? <| mkApp (mkConst declName [u]) type

private def getInst (declName : Name) (u : Level) (type : Expr) : GoalM Expr := do
  synthInstance <| mkApp (mkConst declName [u]) type

private def getBinHomoInst (declName : Name) (u : Level) (type : Expr) : GoalM Expr := do
  synthInstance <| mkApp3 (mkConst declName [u, u, u]) type type type

private def getHSMulIntInst (u : Level) (type : Expr) : GoalM Expr := do
  synthInstance <| mkApp3 (mkConst ``HSMul [0, u, u]) Int.mkType type type

private def getHSMulNatInst (u : Level) (type : Expr) : GoalM Expr := do
  synthInstance <| mkApp3 (mkConst ``HSMul [0, u, u]) Nat.mkType type type

private def checkToFieldDefEq? (leInst? parentInst? childInst? : Option Expr) (toFieldName : Name) (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let some leInst := leInst? | return none
  let some parentInst := parentInst? | return none
  let some childInst := childInst? | return none
  let toField := mkApp3 (mkConst toFieldName [u]) type leInst childInst
  unless (← isDefEqD parentInst toField) do
    reportIssue! (← mkExpectedDefEqMsg parentInst toField)
    return none
  return some childInst

private def ensureToFieldDefEq (parentInst : Expr) (inst : Expr) (toFieldName : Name) (u : Level) (type : Expr) : GoalM Unit := do
  let toField := mkApp2 (mkConst toFieldName [u]) type inst
  ensureDefEq parentInst toField

private def ensureToHomoFieldDefEq (parentInst : Expr) (inst : Expr) (toFieldName : Name) (toHeteroName : Name) (u : Level) (type : Expr)
    (extraType? : Option Expr := none) : GoalM Unit := do
  let toField := mkApp2 (mkConst toFieldName [u]) type inst
  let heteroToField :=
    match extraType? with
    | none => mkApp2 (mkConst toHeteroName [u]) type toField
    | some extraType => mkApp3 (mkConst toHeteroName [0, u]) extraType type toField
  ensureDefEq parentInst heteroToField

private def getHSMulIntFn? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let smulType := mkApp3 (mkConst ``HSMul [0, u, u]) Int.mkType type type
  let some smulInst ← synthInstance? smulType | return none
  internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Int.mkType type type smulInst

private def getHSMulNatFn? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let smulType := mkApp3 (mkConst ``HSMul [0, u, u]) Nat.mkType type type
  let some smulInst ← synthInstance? smulType | return none
  internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Nat.mkType type type smulInst

def getStructId? (type : Expr) : GoalM (Option Nat) := do
  unless (← getConfig).linarith do return none
  if (← isCutsatType type) then return none
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let some u ← getDecLevel? type | return none
    let ringId? ← CommRing.getCommRingId? type
    let leInst? ← getInst? ``LE u type
    let ltInst? ← getInst? ``LT u type
    let lawfulOrderLTInst? ← mkLawfulOrderLTInst? u type ltInst? leInst?
    let isPreorderInst? ← mkIsPreorderInst? u type leInst?
    let isPartialInst? ← mkIsPartialOrderInst? u type leInst?
    let isLinearInst? ← mkIsLinearOrderInst? u type leInst?
    if (← getConfig).ring && ringId?.isSome && isPreorderInst?.isNone then
      /-
      If the type is a `Ring` **and** is not even a preorder **and** `grind ring` is enabled,
      we let `grind ring` process the equalities and disequalities. There is no
      point in using `linarith` in this case.
      **IMPORTANT** We mark the type as a "forbiddenNatModule". It would be pointless to recheck everything in
      in `getNatStructId?`
      -/
      modify' fun s => { s with forbiddenNatModules := s.forbiddenNatModules.insert { expr := type } }
      return none
    let commRingInst? ← getCommRingInst? ringId?
    let ringInst? ← mkRingInst? u type commRingInst?
    let some intModuleInst ← mkIntModuleInst? u type ringInst? | return none
    let addInst ← getBinHomoInst ``HAdd u type
    let addFn ← internalizeFn <| mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type addInst
    let orderedAddInst? ← match leInst?, isPreorderInst? with
      | some leInst, some isPreorderInst =>
        synthInstance? <| mkApp4 (mkConst ``Grind.OrderedAdd [u]) type addInst leInst isPreorderInst
      | _, _ => pure none
    let isPreorderInst? := if orderedAddInst?.isNone then none else isPreorderInst?
    -- preorderInst? may have been reset, check again whether this module is needed.
    if (← getConfig).ring && ringId?.isSome && isPreorderInst?.isNone then
      -- See comment above
      modify' fun s => { s with forbiddenNatModules := s.forbiddenNatModules.insert { expr := type } }
      return none
    let isPartialInst? ← checkToFieldDefEq? leInst? isPreorderInst? isPartialInst? ``Std.IsPartialOrder.toIsPreorder u type
    let isLinearInst? ← checkToFieldDefEq? leInst? isPartialInst? isLinearInst? ``Std.IsLinearOrder.toIsPartialOrder u type
    let addCommGroupInst := mkApp2 (mkConst ``Grind.IntModule.toAddCommGroup [u]) type intModuleInst
    let addCommMonoidInst := mkApp2 (mkConst ``Grind.AddCommGroup.toAddCommMonoid [u]) type addCommGroupInst
    let semiringInst? ← mkSemiringInst? u type ringInst?
    let fieldInst? ← getInst? ``Grind.Field u type
    let one? ← mkOne? u type -- One must be created eagerly
    let orderedRingInst? ← mkOrderedRingInst? u type semiringInst? leInst? ltInst? isPreorderInst?
    let charInst? ← if let some semiringInst := semiringInst? then getIsCharInst? u type semiringInst else pure none
    let noNatDivInst? ← mkNoNatZeroDivInst? u type
    -- TODO: generate the remaining fields on demand
    let zeroInst ← getInst ``Zero u type
    let zero ← internalizeConst <| mkApp2 (mkConst ``Zero.zero [u]) type zeroInst
    let ofNatZeroType := mkApp2 (mkConst ``OfNat [u]) type (mkRawNatLit 0)
    let some ofNatZeroInst ← synthInstance? ofNatZeroType | return none
    -- `ofNatZero` is used internally, we don't need to internalize
    let ofNatZero ← preprocess <| mkApp3 (mkConst ``OfNat.ofNat [u]) type (mkRawNatLit 0) ofNatZeroInst
    ensureDefEq zero ofNatZero
    let subInst ← getBinHomoInst ``HSub u type
    let subFn ← internalizeFn <| mkApp4 (mkConst ``HSub.hSub [u, u, u]) type type type subInst
    let negInst ← getInst ``Neg u type
    let negFn ← internalizeFn <| mkApp2 (mkConst ``Neg.neg [u]) type negInst
    let zsmulInst ← getHSMulIntInst u type
    let zsmulFn ← internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Int.mkType type type zsmulInst
    let nsmulInst ← getHSMulNatInst u type
    let nsmulFn ← internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Nat.mkType type type nsmulInst
    ensureToFieldDefEq zeroInst addCommMonoidInst ``Grind.AddCommMonoid.toZero u type
    ensureToHomoFieldDefEq addInst addCommMonoidInst ``Grind.AddCommMonoid.toAdd ``instHAdd u type
    ensureToHomoFieldDefEq subInst addCommGroupInst ``Grind.AddCommGroup.toSub ``instHSub u type
    ensureToFieldDefEq negInst addCommGroupInst ``Grind.AddCommGroup.toNeg u type
    ensureToHomoFieldDefEq zsmulInst intModuleInst ``Grind.IntModule.zsmul ``instHSMul u type (some Int.mkType)
    ensureToHomoFieldDefEq nsmulInst intModuleInst ``Grind.IntModule.nsmul ``instHSMul u type (some Nat.mkType)
    let leFn? ← if let some leInst := leInst? then
      some <$> (internalizeFn <| mkApp2 (mkConst ``LE.le [u]) type leInst)
    else
      pure none
    let ltFn? ← if let some ltInst := ltInst? then
      some <$> (internalizeFn <| mkApp2 (mkConst ``LT.lt [u]) type ltInst)
    else
      pure none
    let zsmulFn? ← getHSMulIntFn? u type
    let nsmulFn? ← getHSMulNatFn? u type
    let homomulFn? ← if commRingInst?.isSome then
      let mulInst ← getBinHomoInst ``HMul u type
      pure <| some (← internalizeFn <| mkApp4 (mkConst ``HMul.hMul [u, u, u]) type type type mulInst)
    else
      pure none
    let id := (← get').structs.size
    let struct : Struct := {
      id, type, u, intModuleInst, leInst?, ltInst?, lawfulOrderLTInst?, isPreorderInst?,
      orderedAddInst?, isLinearInst?, noNatDivInst?,
      leFn?, ltFn?, addFn, subFn, negFn, zsmulFn, nsmulFn, zsmulFn?, nsmulFn?, zero, one?
      ringInst?, commRingInst?, orderedRingInst?, charInst?, ringId?, fieldInst?, ofNatZero, homomulFn?
    }
    modify' fun s => { s with structs := s.structs.push struct }
    if let some one := one? then
      if ringInst?.isSome then LinearM.run id do
        if orderedRingInst?.isSome then
          -- Create `1` variable, and assert strict lower bound `0 < 1` and `0 ≠ 1`
          let x ← mkVar one (mark := false)
          addZeroLtOne x
          addZeroNeOne x
        else if fieldInst?.isSome || isNonTrivialIsCharInst charInst? then
          -- Create `1` variable, and assert `0 ≠ 1`
          let x ← mkVar one (mark := false)
          addZeroNeOne x
    return some id

private def mkNatModuleInst? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  synthInstance? <| mkApp (mkConst ``Grind.NatModule [u]) type

def getNatStructId? (type : Expr) : GoalM (Option Nat) := do
  unless (← getConfig).linarith do return none
  if (← get').forbiddenNatModules.contains { expr := type } then return none
  if (← isCutsatType type) then return none
  if let some id? := (← get').natTypeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with natTypeIdOf := s.natTypeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let some natModuleInst ← mkNatModuleInst? u type | return none
    let q ← shareCommon (← canon (mkApp2 (mkConst ``Grind.IntModule.OfNatModule.Q [u]) type natModuleInst))
    let some structId ← getStructId? q
      | throwError "`grind` unexpected failure, failure to initialize auxiliary `IntModule`{indentExpr q}"
    let leInst? ← getInst? ``LE u type
    let ltInst? ← getInst? ``LT u type
    let isPreorderInst? ← mkIsPreorderInst? u type leInst?
    let lawfulOrderLTInst? ← mkLawfulOrderLTInst? u type ltInst? leInst?
    let isLinearInst? ← mkIsLinearOrderInst? u type leInst?
    let addInst ← getBinHomoInst ``HAdd u type
    let addFn ← internalizeFn <| mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type addInst
    let orderedAddInst? ← match leInst?, isPreorderInst? with
      | some leInst, some isPreorderInst =>
        synthInstance? <| mkApp4 (mkConst ``Grind.OrderedAdd [u]) type addInst leInst isPreorderInst
      | _, _ => pure none
    let addInst' ← synthInstance <| mkApp (mkConst ``Add [u]) type
    let addRightCancelInst? ← synthInstance? <| mkApp2 (mkConst ``Grind.AddRightCancel [u]) type addInst'
    let toQFn ← internalizeFn <| mkApp2 (mkConst ``Grind.IntModule.OfNatModule.toQ [u]) type natModuleInst
    let zeroInst ← getInst ``Zero u type
    let zero ← internalizeConst <| mkApp2 (mkConst ``Zero.zero [u]) type zeroInst
    let smulInst ← getHSMulNatInst u type
    let smulFn ← internalizeFn <| mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) Nat.mkType type type smulInst
    let rfl_q := mkApp (mkConst ``Eq.refl [.succ u]) q
    let id := (← get').natStructs.size
    let natStruct : NatStruct := {
      id, structId, u, type, natModuleInst,
      leInst?, ltInst?, lawfulOrderLTInst?, isPreorderInst?, isLinearInst?, orderedAddInst?, addRightCancelInst?,
      rfl_q, zero, toQFn, addFn, smulFn
    }
    modify' fun s => { s with natStructs := s.natStructs.push natStruct }
    return some id

end Lean.Meta.Grind.Arith.Linear
