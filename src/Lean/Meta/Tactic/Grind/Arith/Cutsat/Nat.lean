/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.NatInstTesters
public section
namespace Lean.Meta.Grind.Arith.Cutsat

private def natCastRefl (e : Expr) : Expr × Expr :=
  (e, mkApp2 (mkConst ``Eq.refl [1]) Int.mkType e)

/--
Given `e`, returns `(NatCast.natCast e, rfl)`.
The new term `↑e` is internalized before `e` is marked as a solver term: marking replays pending
equalities of `e` into `processNewEq`, which reifies `↑e`.
-/
def mkNatVar (e : Expr) : GoalM (Expr × Expr) := do
  if let some p := (← get').natToIntMap.find? { expr := e } then
    return p
  let e' ← shareCommon (mkIntNatCast e)
  let r := natCastRefl e'
  modify' fun s => { s with
    natToIntMap := s.natToIntMap.insert { expr := e } r
  }
  internalize e' (← getGeneration e)
  cutsatExt.markTerm e
  return r

private def intIte : Expr := mkApp (mkConst ``ite [1]) Int.mkType

/-- Internalizes the `Int` image `e'` of `e : Nat` built by `natToInt`. -/
private def natImage (e e' : Expr) : GoalM Expr := do
  let e' ← shareCommon e'
  internalize e' (← getGeneration e)
  return e'

/-
**Note**: It is safe to use (the more efficient) structural instances tests here because `grind` uses the canonicalizer.
-/
open Structural in
@[specialize] private partial def natToIntAux {m : Type → Type} [Monad m] [MonadLiftT MetaM m]
    (toVar : Expr → m (Expr × Expr)) (image : Expr → Expr → m Expr) (e : Expr) : m (Expr × Expr) := do
  match_expr e with
  | HAdd.hAdd _ _ _ inst a b =>
    if (← isInstHAddNat inst) then
      let (a', h₁) ← natToIntAux toVar image a
      let (b', h₂) ← natToIntAux toVar image b
      let h := mkApp6 (mkConst ``Nat.ToInt.add_congr) a b a' b' h₁ h₂
      return (mkIntAdd a' b', h)
    else
      toVar e
  | HMul.hMul _ _ _ inst a b =>
    if (← isInstHMulNat inst) then
      let (a', h₁) ← natToIntAux toVar image a
      let (b', h₂) ← natToIntAux toVar image b
      let h := mkApp6 (mkConst ``Nat.ToInt.mul_congr) a b a' b' h₁ h₂
      return (mkIntMul a' b', h)
    else
      toVar e
  | HDiv.hDiv _ _ _ inst a b =>
    if (← isInstHDivNat inst) then
      let (a', h₁) ← natToIntAux toVar image a
      let (b', h₂) ← natToIntAux toVar image b
      let h := mkApp6 (mkConst ``Nat.ToInt.div_congr) a b a' b' h₁ h₂
      return (← image e (mkIntDiv a' b'), h)
    else
      toVar e
  | HMod.hMod _ _ _ inst a b =>
    if (← isInstHModNat inst) then
      let (a', h₁) ← natToIntAux toVar image a
      let (b', h₂) ← natToIntAux toVar image b
      let h := mkApp6 (mkConst ``Nat.ToInt.mod_congr) a b a' b' h₁ h₂
      return (← image e (mkIntMod a' b'), h)
    else
      toVar e
  | OfNat.ofNat _ _ _ =>
    if let some n ← getNatValue? e then
      let h := mkApp (mkConst ``Nat.ToInt.natCast_ofNat) e
      return (mkIntLit n, h)
    else
      toVar e
  | HPow.hPow _ _ _ inst a k =>
    if (← isInstHPowNat inst) then
      let (a', h₁) ← natToIntAux toVar image a
      let h := mkApp4 (mkConst ``Nat.ToInt.pow_congr) a k a' h₁
      return (← image e (mkIntPowNat a' k), h)
    else
      toVar e
  | _ => toVar e

/--
Given `a : Nat`, returns `(a', h)` such that `a' : Int`, and `h : NatCast.natCast a = a'`
-/
def natToInt (a : Expr) : GoalM (Expr × Expr) := do
  let toVar (e : Expr) := do
    let t ← if e.hasExprMVar then instantiateMVarsIfMVarApp e else pure e
    let_expr Fin.val n a := t | mkNatVar e
    let alreadyProcessed := (← get').natToIntMap.contains { expr := e }
    let r ← mkNatVar e
    unless alreadyProcessed do pushNewFact <| mkApp2 (mkConst ``Fin.isLt) n a
    return r
  let (b, h) ← natToIntAux toVar natImage a
  let b ← shareCommon b
  return (b, h)

/-- Computes the integer image of a natural-number expression without registering solver terms. -/
def natToIntExpr (e : Expr) : MetaM Expr := do
  let atom (e : Expr) : MetaM (Expr × Expr) := pure (natCastRefl (mkIntNatCast e))
  let (r, _) ← natToIntAux atom (fun _ b => pure b) e
  return r

/--
Given `x` whose denotation is `e`, if `e` is of the form `NatCast.natCast a`,
asserts that it is nonnegative.
-/
def assertNatCast (e : Expr) (x : Var) : GoalM Unit := do
  let_expr NatCast.natCast _ inst a := e | return ()
  let_expr instNatCastInt := inst | return ()
  if a.isAppOf ``OfNat.ofNat then return () -- we don't want to propagate constraints such as `2 ≥ 0`
  if (← get').natDef.contains { expr := a } then return ()
  -- Ensure `a` is marked as a `Nat` variable. This can happen when the `natCast` was introduced by the user.
  discard <| mkNatVar a
  let p := .add (-1) x (.num 0)
  let c := { p, h := .ofNatNonneg a : LeCnstr}
  c.assert

def isNatTerm (e : Expr) : GoalM Bool :=
  return (← get').natToIntMap.contains { expr := e }

/-
**Note**: It is safe to use (the more efficient) structural instances tests here because `grind` uses the canonicalizer.
-/
open Structural in
private partial def isNonneg (e : Expr) : MetaM Bool := do
  match_expr e with
  | OfNat.ofNat _ _ _ =>
    let some n ← getIntValue? e | return false
    return (n ≥ 0 : Bool)
  | HAdd.hAdd _ _ _ i a b => isInstHAddInt i <&&> isNonneg a <&&> isNonneg b
  | HMul.hMul _ _ _ i a b => isInstHMulInt i <&&> isNonneg a <&&> isNonneg b
  | HDiv.hDiv _ _ _ i a b => isInstHDivInt i <&&> isNonneg a <&&> isNonneg b
  | HMod.hMod _ _ _ i a _ => isInstHModInt i <&&> isNonneg a
  | HPow.hPow _ _ _ i a _ => isInstHPowInt i <&&> isNonneg a
  | _ =>
    let_expr NatCast.natCast _ inst _ ← e | return false
    let_expr instNatCastInt := inst | return false
    return true

/-- Given `e : Int`, tries to construct a proof that `e ≥ 0` -/
partial def mkNonnegThm? (e : Expr) : GoalM (Option Expr) := do
  unless (← isNonneg e) do return none
  return some (← go e)
where
  go (e : Expr) : MetaM Expr := do
    match_expr e with
    | OfNat.ofNat _ _ _ => return mkApp2 (mkConst ``Int.Nonneg.num) e eagerReflBoolTrue
    | HAdd.hAdd _ _ _ _ a b => return mkApp4 (mkConst ``Int.Nonneg.add) a b (← go a) (← go b)
    | HMul.hMul _ _ _ _ a b => return mkApp4 (mkConst ``Int.Nonneg.mul) a b (← go a) (← go b)
    | HDiv.hDiv _ _ _ _ a b => return mkApp4 (mkConst ``Int.Nonneg.div) a b (← go a) (← go b)
    | HMod.hMod _ _ _ _ a b => return mkApp3 (mkConst ``Int.Nonneg.mod) a b (← go a)
    | HPow.hPow _ _ _ _ a b => return mkApp3 (mkConst ``Int.Nonneg.pow) a b (← go a)
    | _ =>
      let_expr NatCast.natCast _ _ a ← e | unreachable!
      return mkApp (mkConst ``Int.Nonneg.natCast) a

 /-- Given `x` whose denotation is `e : Int`, tries to assert that `e ≥ 0` -/
def assertNonneg (e : Expr) (x : Var) : GoalM Unit := do
  if e.isAppOf ``NatCast.natCast then return ()
  if e.isAppOf ``OfNat.ofNat then return ()
  let some h ← mkNonnegThm? e | return ()
  let h := mkApp2 (mkConst ``Int.Nonneg.toPoly) e h
  let p := .add (-1) x (.num 0)
  let c := { p, h := .bound h : LeCnstr}
  c.assert

end Lean.Meta.Grind.Arith.Cutsat
