/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr

namespace Lean.Meta.Grind.Arith.CommRing

/-- If `e` is a function application supported by the `CommRing` module, return its type. -/
private def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | HMul.hMul α _ _ _ _ _ => some α
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
      | LE.le _ _ _ _ => true
      | HDiv.hDiv _ _ _ _ _ _ => true
      | HMod.hMod _ _ _ _ _ _ => true
      | _ => false
  else
    true

private partial def toInt? (e : Expr) : RingM (Option Int) := do
  match_expr e with
  | Neg.neg _ i a =>
    if isNegInst (← getRing) i then return (- .) <$> (← toInt? a) else return none
  | IntCast.intCast _ i a =>
    if isIntCastInst (← getRing) i then getIntValue? a else return none
  | NatCast.natCast _ i a =>
    if isNatCastInst (← getRing) i then
      let some v ← getNatValue? a | return none
      return some (Int.ofNat v)
    else
      return none
  | OfNat.ofNat _ n _ =>
    let some v ← getNatValue? n | return none
    return some (Int.ofNat v)
  | _ => return none

private def isDivInst (inst : Expr) : RingM Bool := do
  let some fn := (← getRing).divFn? | return false
  return isSameExpr fn.appArg! inst

/--
Given `e` of the form `@HDiv.hDiv _ _ _ inst a b`,
asserts `a = b * e` if `b` is a numeral.
Otherwise, asserts `b = 0 ∨ a = b * e`
-/
private def processDiv (e inst a b : Expr) : RingM Unit := do
  unless (← isDivInst inst) do return ()
  if (← getRing).divSet.contains (a, b) then return ()
  modifyRing fun s => { s with divSet := s.divSet.insert (a, b) }
  if let some k ← toInt? b then
    let ring ← getRing
    let some fieldInst := ring.fieldInst? | return ()
    if k == 0 then
      pushNewFact <| mkApp3 (mkConst ``Grind.CommRing.div_zero_eq [ring.u]) ring.type fieldInst a
    else if (← hasChar) then
      let (charInst, c) ← getCharInst
      if c == 0 then
        let expected ← mkEq a (mkApp2 ring.mulFn b e)
        pushNewFact <| mkExpectedPropHint
          (mkApp6 (mkConst ``Grind.CommRing.div_int_eq [ring.u]) ring.type fieldInst charInst a (mkIntLit k) reflBoolTrue)
          expected
      else if k % c == 0 then
        let expected ← mkEq e (← denoteNum 0)
        pushNewFact <| mkExpectedPropHint
          (mkApp7 (mkConst ``Grind.CommRing.div_zero_eqC [ring.u]) ring.type (mkNatLit c) fieldInst charInst a (mkIntLit k) reflBoolTrue)
          expected
      else
        let expected ← mkEq a (mkApp2 ring.mulFn b e)
        pushNewFact <| mkExpectedPropHint
          (mkApp7 (mkConst ``Grind.CommRing.div_int_eqC [ring.u]) ring.type (mkNatLit c) fieldInst charInst a (mkIntLit k) reflBoolTrue)
          expected
  else
    -- TODO
    return ()

/--
Returns `true` if `e` is a term `a/b` or `a⁻¹`.
-/
private def internalizeDivInv (e : Expr) : GoalM Bool := do
  match_expr e with
  | HDiv.hDiv α _ _ inst a b =>
    let some ringId ← getRingId? α | return true
    RingM.run ringId do processDiv e inst a b
    return true
  | Inv.inv _α _inst _a =>
    -- TODO
    return true
  | _ => return false

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  if !(← getConfig).ring && !(← getConfig).ringNull then return ()
  if (← internalizeDivInv e) then return ()
  let some type := getType? e | return ()
  if isForbiddenParent parent? then return ()
  let some ringId ← getRingId? type | return ()
  RingM.run ringId do
    let some re ← reify? e | return ()
    trace_goal[grind.ring.internalize] "[{ringId}]: {e}"
    setTermRingId e
    markAsCommRingTerm e
    modifyRing fun s => { s with denote := s.denote.insert { expr := e } re }

end Lean.Meta.Grind.Arith.CommRing
