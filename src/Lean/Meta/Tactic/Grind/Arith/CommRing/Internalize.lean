/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
public import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions

public section

namespace Lean.Meta.Grind.Arith.CommRing

/-- If `e` is a function application supported by the `CommRing` module, return its type. -/
private def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | HMul.hMul α _ _ _ _ _ => some α
  | HSMul.hSMul α β _ _ _ _ =>
    match_expr α with
    | Nat => some β
    | Int => some β
    | _ => none
  | HPow.hPow α β _ _ _ _ =>
    let_expr Nat := β | none
    some α
  | Neg.neg α _ _ => some α
  | OfNat.ofNat α _ _ => some α
  | NatCast.natCast α _ _ => some α
  | IntCast.intCast α _ _ => some α
  | _ => none

private def isForbiddenParent (parent? : Option Expr) : Bool :=
  if let some parent := parent? then
    if getType? parent |>.isSome then
      true
    else
      -- We also ignore the following parents.
      -- Remark: `HDiv` should appear in `getType?` as soon as we add support for `Field`,
      -- `LE.le` linear combinations
      match_expr parent with
      | LT.lt _ _ _ _ => true
      | LE.le _ _ _ _ => true
      | HDiv.hDiv _ _ _ _ _ _ => true
      | HMod.hMod _ _ _ _ _ _ => true
      | _ => false
  else
    false

private partial def toInt? (e : Expr) : RingM (Option Int) := do
  match_expr e with
  | Neg.neg _ i a =>
    if (← isNegInst i) then return (- .) <$> (← toInt? a) else return none
  | IntCast.intCast _ i a =>
    if (← isIntCastInst i) then getIntValue? a else return none
  | NatCast.natCast _ i a =>
    if (← isNatCastInst i) then
      let some v ← getNatValue? a | return none
      return some (Int.ofNat v)
    else
      return none
  | OfNat.ofNat _ n _ =>
    let some v ← getNatValue? n | return none
    return some (Int.ofNat v)
  | _ => return none

private def isInvInst (inst : Expr) : RingM Bool := do
  if (← getRing).fieldInst?.isNone then return false
  return isSameExpr (← getInvFn).appArg! inst

/--
Given `e` of the form `@Inv.inv _ inst a`,
asserts `a * a⁻¹ = 1` if `a` is a numeral.
Otherwise, asserts `if a = 0 then a⁻¹ = 0 else a * a⁻¹ = 1`
-/
private def processInv (e inst a : Expr) : RingM Unit := do
  unless (← isInvInst inst) do return ()
  let ring ← getRing
  let some fieldInst := ring.fieldInst? | return ()
  if (← getRing).invSet.contains a then return ()
  modifyRing fun s => { s with invSet := s.invSet.insert a }
  if let some k ← toInt? a then
    assert! k != 0 -- We have the normalization rule `Field.inv_zero`
    if (← hasChar) then
      let (charInst, c) ← getCharInst
      if c == 0 then
        let expected ← mkEq (mkApp2 (← getMulFn) a e) (← denoteNum 1)
        pushNewFact <| mkExpectedPropHint
          (mkApp5 (mkConst ``Grind.CommRing.inv_int_eq [ring.u]) ring.type fieldInst charInst (mkIntLit k) eagerReflBoolTrue)
          expected
      else if k % c == 0 then
        let expected ← mkEq e (← denoteNum 0)
        pushNewFact <| mkExpectedPropHint
          (mkApp6 (mkConst ``Grind.CommRing.inv_zero_eqC [ring.u]) ring.type (mkNatLit c) fieldInst charInst (mkIntLit k) eagerReflBoolTrue)
          expected
      else
        let expected ← mkEq (mkApp2 (← getMulFn) a e) (← denoteNum 1)
        pushNewFact <| mkExpectedPropHint
          (mkApp6 (mkConst ``Grind.CommRing.inv_int_eqC [ring.u]) ring.type (mkNatLit c) fieldInst charInst (mkIntLit k) eagerReflBoolTrue)
          expected
      return ()
  pushNewFact <| mkApp3 (mkConst ``Grind.CommRing.inv_split [ring.u]) ring.type fieldInst a

/-- Returns `true` if `e` is a term `a⁻¹`. -/
private def internalizeInv (e : Expr) : GoalM Bool := do
  match_expr e with
  | Inv.inv α inst a =>
    let some ringId ← getRingId? α | return true
    RingM.run ringId do processInv e inst a
    return true
  | _ => return false

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  if !(← getConfig).ring then return ()
  if isIntModuleVirtualParent parent? then
    -- `e` is an auxiliary term used to convert `CommRing` to `IntModule`
    return ()
  if (← internalizeInv e) then return ()
  let some type := getType? e | return ()
  if isForbiddenParent parent? then return ()
  if let some ringId ← getRingId? type then RingM.run ringId do
    let some re ← reify? e | return ()
    trace_goal[grind.ring.internalize] "[{ringId}]: {e}"
    setTermRingId e
    markAsCommRingTerm e
    modifyRing fun s => { s with
      denote := s.denote.insert { expr := e } re
      denoteEntries := s.denoteEntries.push (e, re)
    }
  else if let some semiringId ← getSemiringId? type then SemiringM.run semiringId do
    let some re ← sreify? e | return ()
    trace_goal[grind.ring.internalize] "semiring [{semiringId}]: {e}"
    setTermSemiringId e
    markAsCommRingTerm e
    modifySemiring fun s => { s with denote := s.denote.insert { expr := e } re }

end Lean.Meta.Grind.Arith.CommRing
