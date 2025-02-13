/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Linear
import Lean.Util.SortExprs
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

/-- Applies the given variable permutation to `e` -/
def Expr.applyPerm (perm : Lean.Perm) (e : Expr) : Expr :=
  go e
where
  go : Expr → Expr
    | .num v    => .num v
    | .var i    => .var (perm[(i : Nat)]?.getD i)
    | .neg a    => .neg (go a)
    | .add a b  => .add (go a) (go b)
    | .sub a b  => .sub (go a) (go b)
    | .mulL k a => .mulL k (go a)
    | .mulR a k => .mulR (go a) k

/-- Applies the given variable permutation to the given expression constraint. -/
def ExprCnstr.applyPerm (perm : Lean.Perm) : ExprCnstr → ExprCnstr
  | .eq a b => .eq (a.applyPerm perm) (b.applyPerm perm)
  | .le a b => .le (a.applyPerm perm) (b.applyPerm perm)

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

partial def toLinearExpr (e : Expr) : M LinearExpr := do
  match e with
  | .mdata _ e            => toLinearExpr e
  | .app ..               => visit e
  | .mvar ..              => visit e
  | _                     => addAsVar e
where
  visit (e : Expr) : M LinearExpr := do
    let mul (a b : Expr) := do
      match (← getIntValue? a) with
      | some k => return .mulL k (← toLinearExpr b)
      | none => match (← getIntValue? b) with
        | some k => return .mulR (← toLinearExpr a) k
        | none => addAsVar e
    match_expr e with
    | OfNat.ofNat _ _ _ =>
      if let some n ← getIntValue? e then return .num n
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
      if (← isInstHSubInt i) then return .sub (← toLinearExpr a) (← toLinearExpr b)
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
    let a ← toLinearExpr a
    let b ← toLinearExpr b
    match a, b with
    /-
    We do not want to convert `x = y` into `x + -1*y = 0`.
    Similarly, we don't want to convert `x = 3` into `x + -3 = 0`.
    `grind` and other tactics have better support for this kind of equalities.
    -/
    | .var _, .var _ | .var _, .num _ | .num _, .var _ => failure
    | _, _ => return .eq a b
  | Int.le a b =>
    return .le (← toLinearExpr a) (← toLinearExpr b)
  | Int.lt a b =>
    return .le (.add (← toLinearExpr a) (.num 1)) (← toLinearExpr b)
  | LE.le _ i a b =>
    guard (← isInstLEInt i)
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

def toLinearExpr (e : Expr) : MetaM (LinearExpr × Array Expr) := do
  let (e, atoms) ← ToLinear.run (ToLinear.toLinearExpr e)
  if atoms.size == 1 then
    return (e, atoms)
  else
    let (atoms, perm) := sortExprs atoms
    let e := e.applyPerm perm
    return (e, atoms)

def toLinearCnstr? (e : Expr) : MetaM (Option (LinearCnstr × Array Expr)) := do
  let (some c, atoms) ← ToLinear.run (ToLinear.toLinearCnstr? e)
    | return none
  if atoms.size <= 1 then
    return some (c, atoms)
  else
    let (atoms, perm) := sortExprs atoms
    let c := c.applyPerm perm
    return some (c, atoms)

def toContextExpr (ctx : Array Expr) : Expr :=
  if h : 0 < ctx.size then
    RArray.toExpr (mkConst ``Int) id (RArray.ofArray ctx h)
  else
    RArray.toExpr (mkConst ``Int) id (RArray.leaf (mkIntLit 0))

end Lean.Meta.Linear.Int
