/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Simp.Arith.Nat.Basic
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm

namespace Lean.Meta.Grind.Arith.Cutsat

def mkNatVar (e : Expr) : GoalM (Expr × Expr) := do
  if let some p := (← get').natToIntMap.find? { expr := e } then
    return p
  let e' := mkIntNatCast e
  let he := mkApp (mkApp (mkConst ``Eq.refl [1]) Int.mkType) e'
  let r := (e', he)
  modify' fun s => { s with
    natToIntMap := s.natToIntMap.insert { expr := e } r
  }
  markAsCutsatTerm e
  return r

private def intIte : Expr := mkApp (mkConst ``ite [1]) Int.mkType

private partial def natToInt' (e : Expr) : GoalM (Expr × Expr) := do
  match_expr e with
  | HAdd.hAdd _ _ _ inst a b =>
    if (← isInstHAddNat inst) then
      let (a', h₁) ← natToInt' a
      let (b', h₂) ← natToInt' b
      let h := mkApp6 (mkConst ``Nat.ToInt.add_congr) a b a' b' h₁ h₂
      return (mkIntAdd a' b', h)
    else
      mkNatVar e
  | HMul.hMul _ _ _ inst a b =>
    if (← isInstHMulNat inst) then
      let (a', h₁) ← natToInt' a
      let (b', h₂) ← natToInt' b
      let h := mkApp6 (mkConst ``Nat.ToInt.mul_congr) a b a' b' h₁ h₂
      return (mkIntMul a' b', h)
    else
      mkNatVar e
  | HDiv.hDiv _ _ _ inst a b =>
    if (← isInstHDivNat inst) then
      let (a', h₁) ← natToInt' a
      let (b', h₂) ← natToInt' b
      let h := mkApp6 (mkConst ``Nat.ToInt.div_congr) a b a' b' h₁ h₂
      return (mkIntDiv a' b', h)
    else
      mkNatVar e
  | HMod.hMod _ _ _ inst a b =>
    if (← isInstHModNat inst) then
      let (a', h₁) ← natToInt' a
      let (b', h₂) ← natToInt' b
      let h := mkApp6 (mkConst ``Nat.ToInt.mod_congr) a b a' b' h₁ h₂
      return (mkIntMod a' b', h)
    else
      mkNatVar e
  | OfNat.ofNat _ _ _ =>
    if let some n ← getNatValue? e then
      let h := mkApp (mkConst ``Nat.ToInt.natCast_ofNat) e
      return (mkIntLit n, h)
    else
      mkNatVar e
  | HPow.hPow _ _ _ inst a k =>
    if (← isInstHPowNat inst) then
      let (a', h₁) ← natToInt' a
      let h := mkApp4 (mkConst ``Nat.ToInt.pow_congr) a k a' h₁
      return (mkIntPowNat a' k, h)
    else
      mkNatVar e
  | HSub.hSub _ _ _ inst a b =>
    if (← isInstHSubNat inst) then
      let (a', h₁) ← natToInt' a
      let (b', h₂) ← natToInt' b
      let lhs := mkIntAdd b' (mkIntMul (mkIntLit (-1)) a')
      let rhs := mkIntLit 0
      let c := mkIntLE lhs rhs
      let dec := mkApp2 (mkConst ``Int.decLe) lhs rhs
      let r := mkApp4 intIte c dec (mkIntSub a' b') (mkIntLit 0)
      let h := mkApp6 (mkConst ``Nat.ToInt.sub_congr) a b a' b' h₁ h₂
      -- We need to simplify because `cutsat` expects arithmetic to be in normal form,
      -- nested instances to be marked and canonicalized
      let r ← simpCore r
      let h ← if let some h' := r.proof? then mkEqTrans h h' else pure h
      let r ← markNestedSubsingletons r.expr
      return (r, h)
    else
      mkNatVar e
  | _ => mkNatVar e

/--
Given `a : Nat`, returns `(a', h)` such that `a' : Int`, and `h : NatCast.natCast a = a'`
-/
def natToInt (a : Expr) : GoalM (Expr × Expr) := do
  let (b, h) ← natToInt' a
  let b ← shareCommon b
  return (b, h)

/--
Given `x` whose denotation is `e`, if `e` is of the form `NatCast.natCast a`,
asserts that it is nonnegative.
-/
def assertNatCast (e : Expr) (x : Var) : GoalM Unit := do
  let_expr NatCast.natCast _ inst a := e | return ()
  let_expr instNatCastInt := inst | return ()
  if a.isAppOf ``OfNat.ofNat then return () -- we don't want to propagate constraints such as `2 ≥ 0`
  if (← get').natDef.contains { expr := a } then return ()
  let p := .add (-1) x (.num 0)
  let c := { p, h := .ofNatNonneg a : LeCnstr}
  c.assert

def isNatTerm (e : Expr) : GoalM Bool :=
  return (← get').natToIntMap.contains { expr := e }

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
    | OfNat.ofNat _ _ _ => return mkApp2 (mkConst ``Int.Nonneg.num) e reflBoolTrue
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
