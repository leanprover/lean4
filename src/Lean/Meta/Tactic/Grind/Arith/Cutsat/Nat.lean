/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Simp.Arith.Nat.Basic
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Foreign
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm

namespace Int.OfNat
open Lean

protected def toExpr (e : Expr) : Lean.Expr :=
  open Int.OfNat.Expr in
  match e with
  | .num v    => mkApp (mkConst ``num) (mkNatLit v)
  | .var i    => mkApp (mkConst ``var) (mkNatLit i)
  | .add a b  => mkApp2 (mkConst ``add) (OfNat.toExpr a) (OfNat.toExpr b)
  | .mul a b  => mkApp2 (mkConst ``mul) (OfNat.toExpr a) (OfNat.toExpr b)
  | .div a b  => mkApp2 (mkConst ``div) (OfNat.toExpr a) (OfNat.toExpr b)
  | .mod a b  => mkApp2 (mkConst ``mod) (OfNat.toExpr a) (OfNat.toExpr b)

instance : ToExpr OfNat.Expr where
  toExpr a := OfNat.toExpr a
  toTypeExpr := mkConst ``OfNat.Expr

open Lean.Meta.Grind
open Lean.Meta.Grind.Arith.Cutsat

open Meta

def Expr.denoteAsIntExpr (ctx : PArray Lean.Expr) (e : Expr) : GoalM Lean.Expr :=
  shareCommon (go e)
where
  go (e : Expr) : Lean.Expr :=
    match e with
    | .num v    => mkIntLit v
    | .var i    => mkIntNatCast ctx[i]!
    | .add a b  => mkIntAdd (go a) (go b)
    | .mul a b  => mkIntMul (go a) (go b)
    | .div a b  => mkIntDiv (go a) (go b)
    | .mod a b  => mkIntMod (go a) (go b)

partial def toOfNatExpr (e : Lean.Expr) : GoalM Expr := do
  let mkVar (e : Lean.Expr) : GoalM Expr := do
    let x ← mkForeignVar e .nat
    return .var x
  match_expr e with
  | OfNat.ofNat _ _ _ =>
    if let some n ← getNatValue? e then
      return .num n
    else
      mkVar e
  | HAdd.hAdd _ _ _ i a b =>
    if (← isInstHAddNat i) then return .add (← toOfNatExpr a) (← toOfNatExpr b)
    else mkVar e
  | HMul.hMul _ _ _ i a b =>
    if (← isInstHMulNat i) then return .mul (← toOfNatExpr a) (← toOfNatExpr b)
    else mkVar e
  | HDiv.hDiv _ _ _ i a b =>
    if (← isInstHDivNat i) then return .div (← toOfNatExpr a) (← toOfNatExpr b)
    else mkVar e
  | HMod.hMod _ _ _ i a b =>
    if (← isInstHModNat i) then return .mod (← toOfNatExpr a) (← toOfNatExpr b)
    else mkVar e
  | _ => mkVar e

/--
Given `e` of the form `lhs ≤ rhs` where `lhs` and `rhs` have type `Nat`,
returns `(lhs, rhs)` where `lhs` and `rhs` are `Int.OfNat.Expr`.
-/
def toIntLe? (e : Lean.Expr) : GoalM (Option (Expr × Expr)) := do
  let_expr LE.le _ inst lhs rhs := e | return none
  unless (← isInstLENat inst) do return none
  let lhs ← toOfNatExpr lhs
  let rhs ← toOfNatExpr rhs
  return some (lhs, rhs)

def toIntDvd? (e : Lean.Expr) : GoalM (Option (Nat × Expr)) := do
  let_expr Dvd.dvd _ inst a b := e | return none
  unless (← isInstDvdNat inst) do return none
  let some d ← getNatValue? a
    | reportIssue! "non-linear divisibility constraint found{indentExpr e}"
      return none
  let b ← toOfNatExpr b
  return some (d, b)

def toIntEq (lhs rhs : Lean.Expr) : GoalM (Expr × Expr) := do
  let lhs ← toOfNatExpr lhs
  let rhs ← toOfNatExpr rhs
  return (lhs, rhs)

/--
Given `e` of type `Int`, tries to compute `a : Int.OfNat.Expr` s.t.
`a.denoteAsInt ctx` is `e`
-/
partial def ofDenoteAsIntExpr? (e : Lean.Expr) : OptionT GoalM Expr := do
  match_expr e with
  | OfNat.ofNat _ _ _ =>
    let some n ← getIntValue? e | failure
    guard (n ≥ 0)
    return .num n.toNat
  | HAdd.hAdd _ _ _ i a b =>
    guard (← isInstHAddInt i)
    return .add (← ofDenoteAsIntExpr? a) (← ofDenoteAsIntExpr? b)
  | HMul.hMul _ _ _ i a b =>
    guard (← isInstHMulInt i)
    return .mul (← ofDenoteAsIntExpr? a) (← ofDenoteAsIntExpr? b)
  | HDiv.hDiv _ _ _ i a b =>
    guard (← isInstHDivInt i)
    return .div (← ofDenoteAsIntExpr? a) (← ofDenoteAsIntExpr? b)
  | HMod.hMod _ _ _ i a b =>
    guard (← isInstHModInt i)
    return .mod (← ofDenoteAsIntExpr? a) (← ofDenoteAsIntExpr? b)
  | _ =>
    let_expr NatCast.natCast _ inst a ← e | failure
    let_expr instNatCastInt := inst | failure
    let x ← mkForeignVar a .nat
    return .var x

end Int.OfNat

namespace Lean.Meta.Grind.Arith.Cutsat
/--
If `e` is of the form `a.denoteAsInt ctx` for some `a` and `ctx`,
assert that `e` is nonnegative.
-/
def assertDenoteAsIntNonneg (e : Expr) : GoalM Unit := withIncRecDepth do
  if e.isAppOf ``NatCast.natCast then return ()
  let some rhs ← Int.OfNat.ofDenoteAsIntExpr? e |>.run | return ()
  let gen ← getGeneration e
  let ctx ← getForeignVars .nat
  let lhs' : Int.Linear.Expr := .num 0
  let rhs' ← toLinearExpr (← rhs.denoteAsIntExpr ctx) gen
  let p := lhs'.sub rhs' |>.norm
  let c := { p, h := .denoteAsIntNonneg rhs rhs' : LeCnstr }
  c.assert

/--
Given `x` whose denotation is `e`, if `e` is of the form `NatCast.natCast a`,
asserts that it is nonnegative.
-/
def assertNatCast (e : Expr) (x : Var) : GoalM Unit := do
  let_expr NatCast.natCast _ inst a := e | return ()
  let_expr instNatCastInt := inst | return ()
  if (← get').foreignDef.contains { expr := a } then return ()
  let n ← mkForeignVar a .nat
  let p := .add (-1) x (.num 0)
  let c := { p, h := .denoteAsIntNonneg (.var n) (.var x) : LeCnstr}
  c.assert

end Lean.Meta.Grind.Arith.Cutsat
