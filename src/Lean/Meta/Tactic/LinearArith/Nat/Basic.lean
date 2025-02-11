/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.SortExprs
import Lean.Meta.Check
import Lean.Meta.Offset
import Lean.Meta.AppBuilder
import Lean.Meta.KExprMap
import Lean.Data.RArray

namespace Nat.Linear

/-- Applies the given variable permutation to `e` -/
def Expr.applyPerm (perm : Lean.Perm) (e : Expr) : Expr :=
  go e
where
  go : Expr → Expr
    | .num v    => .num v
    | .var i    => .var (perm[(i : Nat)]?.getD i)
    | .add a b  => .add (go a) (go b)
    | .mulL k a => .mulL k (go a)
    | .mulR a k => .mulR (go a) k

/-- Applies the given variable permutation to the given expression constraint. -/
def ExprCnstr.applyPerm (perm : Lean.Perm) : ExprCnstr → ExprCnstr
  | { eq, lhs, rhs } => { eq, lhs := lhs.applyPerm perm, rhs := rhs.applyPerm perm }

end Nat.Linear

namespace Lean.Meta.Linear.Nat

deriving instance Repr for Nat.Linear.Expr
deriving instance Repr for Nat.Linear.ExprCnstr
deriving instance Repr for Nat.Linear.PolyCnstr

abbrev LinearExpr  := Nat.Linear.Expr
abbrev LinearCnstr := Nat.Linear.ExprCnstr
abbrev PolyExpr := Nat.Linear.Poly

def LinearExpr.toExpr (e : LinearExpr) : Expr :=
  open Nat.Linear.Expr in
  match e with
  | num v    => mkApp (mkConst ``num) (mkNatLit v)
  | var i    => mkApp (mkConst ``var) (mkNatLit i)
  | add a b  => mkApp2 (mkConst ``add) (toExpr a) (toExpr b)
  | mulL k a => mkApp2 (mkConst ``mulL) (mkNatLit k) (toExpr a)
  | mulR a k => mkApp2 (mkConst ``mulR) (toExpr a) (mkNatLit k)

instance : ToExpr LinearExpr where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``Nat.Linear.Expr

protected def LinearCnstr.toExpr (c : LinearCnstr) : Expr :=
   mkApp3 (mkConst ``Nat.Linear.ExprCnstr.mk) (toExpr c.eq) (LinearExpr.toExpr c.lhs) (LinearExpr.toExpr c.rhs)

instance : ToExpr LinearCnstr where
  toExpr a   := a.toExpr
  toTypeExpr := mkConst ``Nat.Linear.ExprCnstr

open Nat.Linear.Expr in
def LinearExpr.toArith (ctx : Array Expr) (e : LinearExpr) : MetaM Expr := do
  match e with
  | num v    => return mkNatLit v
  | var i    => return ctx[i]!
  | add a b  => return mkNatAdd (← toArith ctx a) (← toArith ctx b)
  | mulL k a => return mkNatMul (mkNatLit k) (← toArith ctx a)
  | mulR a k => return mkNatMul (← toArith ctx a) (mkNatLit k)

def LinearCnstr.toArith (ctx : Array Expr) (c : LinearCnstr) : MetaM Expr := do
  if c.eq then
    return mkNatEq (← LinearExpr.toArith ctx c.lhs) (← LinearExpr.toArith ctx c.rhs)
  else
    return mkNatLE (← LinearExpr.toArith ctx c.lhs) (← LinearExpr.toArith ctx c.rhs)

namespace ToLinear

structure State where
  varMap : KExprMap Nat := {} -- It should be fine to use `KExprMap` here because the mapping should be small and few HeadIndex collisions.
  vars   : Array Expr := #[]

abbrev M := StateRefT State MetaM

open Nat.Linear.Expr

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
  | .lit (.natVal n)      => return num n
  | .mdata _ e            => toLinearExpr e
  | .const ``Nat.zero ..  => return num 0
  | .app ..               => visit e
  | .mvar ..              => visit e
  | _                     => addAsVar e
where
  visit (e : Expr) : M LinearExpr := do
    let mul (a b : Expr) := do
      match (← evalNat a |>.run) with
      | some k => return mulL k (← toLinearExpr b)
      | none => match (← evalNat b |>.run) with
        | some k => return mulR (← toLinearExpr a) k
        | none => addAsVar e
    match_expr e with
    | OfNat.ofNat _ n i =>
      if (← isInstOfNatNat i) then toLinearExpr n
      else addAsVar e
    | Nat.succ a => return inc (← toLinearExpr a)
    | Nat.add a b => return add (← toLinearExpr a) (← toLinearExpr b)
    | Add.add _ i a b =>
      if (← isInstAddNat i) then return add (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | HAdd.hAdd _ _ _ i a b =>
      if (← isInstHAddNat i) then return add (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | Nat.mul a b => mul a b
    | Mul.mul _ i a b =>
      if (← isInstMulNat i) then mul a b
      else addAsVar e
    | HMul.hMul _ _ _ i a b =>
      if (← isInstHMulNat i) then mul a b
      else addAsVar e
    | _ => addAsVar e

partial def toLinearCnstr? (e : Expr) : M (Option LinearCnstr) := OptionT.run do
  match_expr e with
  | Eq α a b =>
    let_expr Nat ← α | failure
    return { eq := true, lhs := (← toLinearExpr a), rhs := (← toLinearExpr b) }
  | Nat.le a b =>
    return { eq := false, lhs := (← toLinearExpr a), rhs := (← toLinearExpr b) }
  | Nat.lt a b =>
    return { eq := false, lhs := (← toLinearExpr a).inc, rhs := (← toLinearExpr b) }
  | LE.le _ i a b =>
    guard (← isInstLENat i)
    return { eq := false, lhs := (← toLinearExpr a), rhs := (← toLinearExpr b) }
  | LT.lt _ i a b =>
    guard (← isInstLTNat i)
    return { eq := false, lhs := (← toLinearExpr a).inc, rhs := (← toLinearExpr b) }
  | GE.ge _ i a b =>
    guard (← isInstLENat i)
    return { eq := false, lhs := (← toLinearExpr b), rhs := (← toLinearExpr a) }
  | GT.gt _ i a b =>
    guard (← isInstLTNat i)
    return { eq := false, lhs := (← toLinearExpr b).inc, rhs := (← toLinearExpr a) }
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
    RArray.toExpr (mkConst ``Nat) id (RArray.ofArray ctx h)
  else
    RArray.toExpr (mkConst ``Nat) id (RArray.leaf (mkNatLit 0))

namespace Lean.Meta.Linear.Nat
