/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Simp.Arith.Nat.Basic
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

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

def Expr.denoteAsIntExpr (ctx : Array Lean.Expr) (e : Expr) : Lean.Expr :=
  match e with
  | .num v    => mkIntLit v
  | .var i    => mkIntNatCast ctx[i]!
  | .add a b  => mkIntAdd (denoteAsIntExpr ctx a) (denoteAsIntExpr ctx b)
  | .mul a b  => mkIntMul (denoteAsIntExpr ctx a) (denoteAsIntExpr ctx b)
  | .div a b  => mkIntDiv (denoteAsIntExpr ctx a) (denoteAsIntExpr ctx b)
  | .mod a b  => mkIntMod (denoteAsIntExpr ctx a) (denoteAsIntExpr ctx b)

open Lean.Meta.Grind

structure OfNat.State where
  ctx : Array Lean.Expr := #[]
  map : Std.HashMap ENodeKey Var := {}

abbrev M := StateRefT OfNat.State MetaM

open Meta

partial def toOfNatExpr (e : Lean.Expr) : M Expr := do
  let mkVar (e : Lean.Expr) : M Expr := do
    if let some x := (← get).map.get? { expr := e } then
      return .var x
    else
      let x := (← get).ctx.size
      modify fun s => { s with ctx := s.ctx.push e, map := s.map.insert { expr := e} x }
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
returns `(lhs, rhs, ctx)` where `lhs` and `rhs` are `Int.OfNat.Expr` and `ctx` is the context.
-/
def toIntLe? (e : Lean.Expr) : MetaM (Option (Expr × Expr × Array Lean.Expr)) := do
  let_expr LE.le _ inst lhs rhs := e | return none
  unless (← isInstLENat inst) do return none
  let ((lhs, rhs), s) ← conv lhs rhs |>.run {}
  return some (lhs, rhs, s.ctx)
where
  conv (lhs rhs : Lean.Expr) : M (Expr × Expr) :=
    return (← toOfNatExpr lhs, ← toOfNatExpr rhs)

end Int.OfNat
