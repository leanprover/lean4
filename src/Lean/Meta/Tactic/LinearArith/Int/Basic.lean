/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Linear
import Lean.Meta.Check
import Lean.Meta.Offset
import Lean.Meta.IntInstTesters
import Lean.Meta.AppBuilder
import Lean.Meta.KExprMap
import Lean.Data.RArray

namespace Int.Linear

/-- Converts the linear polynomial into the "simplified" expression -/
def Poly.toExpr (p : Poly) : Expr :=
  go none p
where
  go : Option Expr → Poly → Expr
    | none,   .num k     => .num k
    | some e, .num 0     => e
    | some e, .num k     => .add e (.num k)
    | none,   .add 1 x p => go (some (.var x)) p
    | none,   .add k x p => go (some (.mulL k (.var x))) p
    | some e, .add 1 x p => go (some (.add e (.var x))) p
    | some e, .add k x p => go (some (.add e (.mulL k (.var x)))) p

def PolyCnstr.toExprCnstr : PolyCnstr → ExprCnstr
  | .eq p => .eq p.toExpr (.num 0)
  | .le p => .le p.toExpr (.num 0)

end Int.Linear

namespace Lean.Meta.Linear.Int

deriving instance Repr for Int.Linear.Poly
deriving instance Repr for Int.Linear.Expr
deriving instance Repr for Int.Linear.ExprCnstr
deriving instance Repr for Int.Linear.PolyCnstr

abbrev LinearExpr  := Int.Linear.Expr
abbrev LinearCnstr := Int.Linear.ExprCnstr
abbrev PolyExpr    := Int.Linear.Poly

def LinearExpr.toExpr (e : LinearExpr) : Expr :=
  open Int.Linear.Expr in
  match e with
  | .num v    => mkApp (mkConst ``num) (Lean.toExpr v)
  | .var i    => mkApp (mkConst ``var) (mkNatLit i)
  | .neg a    => mkApp (mkConst ``neg) (toExpr a)
  | .add a b  => mkApp2 (mkConst ``add) (toExpr a) (toExpr b)
  | .sub a b  => mkApp2 (mkConst ``sub) (toExpr a) (toExpr b)
  | .mulL k a => mkApp2 (mkConst ``mulL) (Lean.toExpr k) (toExpr a)
  | .mulR a k => mkApp2 (mkConst ``mulR) (toExpr a) (Lean.toExpr k)

instance : ToExpr LinearExpr where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``Int.Linear.Expr

protected def LinearCnstr.toExpr (c : LinearCnstr) : Expr :=
   open Int.Linear.ExprCnstr in
   match c with
   | .eq e₁ e₂ => mkApp2 (mkConst ``eq) (toExpr e₁) (toExpr e₂)
   | .le e₁ e₂ => mkApp2 (mkConst ``le) (toExpr e₁) (toExpr e₂)

instance : ToExpr LinearCnstr where
  toExpr a   := a.toExpr
  toTypeExpr := mkConst ``Int.Linear.ExprCnstr

open Int.Linear.Expr in
def LinearExpr.toArith (ctx : Array Expr) (e : LinearExpr) : MetaM Expr := do
  match e with
  | .num v    => return Lean.toExpr v
  | .var i    => return ctx[i]!
  | .neg a    => return mkIntNeg (← toArith ctx a)
  | .add a b  => return mkIntAdd (← toArith ctx a) (← toArith ctx b)
  | .sub a b  => return mkIntSub (← toArith ctx a) (← toArith ctx b)
  | .mulL k a => return mkIntMul (Lean.toExpr k) (← toArith ctx a)
  | .mulR a k => return mkIntMul (← toArith ctx a) (Lean.toExpr k)

def LinearCnstr.toArith (ctx : Array Expr) (c : LinearCnstr) : MetaM Expr := do
  match c with
  | .eq e₁ e₂ => return mkIntEq (← LinearExpr.toArith ctx e₁) (← LinearExpr.toArith ctx e₂)
  | .le e₁ e₂ => return mkIntLE (← LinearExpr.toArith ctx e₁) (← LinearExpr.toArith ctx e₂)

namespace ToLinear

structure State where
  varMap : KExprMap Nat := {} -- It should be fine to use `KExprMap` here because the mapping should be small and few HeadIndex collisions.
  vars   : Array Expr := #[]

abbrev M := StateRefT State MetaM

open Int.Linear.Expr

def addAsVar (e : Expr) : M LinearExpr := do
  if let some x ← (← get).varMap.find? e then
    return var x
  else
    let x := (← get).vars.size
    let s ← get
    set { varMap := (← s.varMap.insert e x), vars := s.vars.push e : State }
    return var x

private def toInt? (e : Expr) : MetaM (Option Int) := do
  let_expr OfNat.ofNat _ n i ← e | return none
  unless (← isInstOfNatInt i) do return none
  let some n ← evalNat n |>.run | return none
  return some (Int.ofNat n)

partial def toLinearExpr (e : Expr) : M LinearExpr := do
  match e with
  | .mdata _ e            => toLinearExpr e
  | .app ..               => visit e
  | .mvar ..              => visit e
  | _                     => addAsVar e
where
  visit (e : Expr) : M LinearExpr := do
    let mul (a b : Expr) := do
      match (← toInt? a) with
      | some k => return .mulL k (← toLinearExpr b)
      | none => match (← toInt? b) with
        | some k => return .mulR (← toLinearExpr a) k
        | none => addAsVar e
    match_expr e with
    | OfNat.ofNat _ n i =>
      if (← isInstOfNatInt i) then toLinearExpr n
      else addAsVar e
    | Int.neg a => return .neg (← toLinearExpr a)
    | Neg.neg _ i a =>
      if (← isInstNegInt i) then return .neg (← toLinearExpr a)
      else addAsVar e
    | Int.add a b => return .add (← toLinearExpr a) (← toLinearExpr b)
    | Add.add _ i a b =>
      if (← isInstAddInt i) then return .add (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | HAdd.hAdd _ _ _ i a b =>
      if (← isInstHAddInt i) then return .add (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | Int.sub a b => return .sub (← toLinearExpr a) (← toLinearExpr b)
    | Sub.sub _ i a b =>
      if (← isInstSubInt i) then return .sub (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | HSub.hSub _ _ _ i a b =>
      if (← isInstSubInt i) then return .sub (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | Int.mul a b => mul a b
    | Mul.mul _ i a b =>
      if (← isInstMulInt i) then mul a b
      else addAsVar e
    | HMul.hMul _ _ _ i a b =>
      if (← isInstHMulInt i) then mul a b
      else addAsVar e
    | _ => addAsVar e

partial def toLinearCnstr? (e : Expr) : M (Option LinearCnstr) := OptionT.run do
  match_expr e with
  | Eq α a b =>
    let_expr Int ← α | failure
    return .eq (← toLinearExpr a) (← toLinearExpr b)
  | Int.le a b =>
    return .le (← toLinearExpr a) (← toLinearExpr b)
  | Int.lt a b =>
    return .le (.add (← toLinearExpr a) (.num 1)) (← toLinearExpr b)
  | LE.le _ i a b =>
    guard (← isInstLENat i)
    return .le (← toLinearExpr a) (← toLinearExpr b)
  | LT.lt _ i a b =>
    guard (← isInstLTInt i)
    return .le (.add (← toLinearExpr a) (.num 1)) (← toLinearExpr b)
  | GE.ge _ i a b =>
    guard (← isInstLEInt i)
    return .le (← toLinearExpr b) (← toLinearExpr a)
  | GT.gt _ i a b =>
    guard (← isInstLTInt i)
    return .le (.add (← toLinearExpr b) (.num 1)) (← toLinearExpr a)
  | _ => failure

def run (x : M α) : MetaM (α × Array Expr) := do
  let (a, s) ← x.run {}
  return (a, s.vars)

end ToLinear

export ToLinear (toLinearCnstr? toLinearExpr)

def toContextExpr (ctx : Array Expr) : Expr :=
  if h : 0 < ctx.size then
    RArray.toExpr (mkConst ``Int) id (RArray.ofArray ctx h)
  else
    RArray.toExpr (mkConst ``Int) id (RArray.leaf (mkIntLit 0))

end Lean.Meta.Linear.Int
