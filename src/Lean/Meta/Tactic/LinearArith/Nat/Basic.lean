/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Check
import Lean.Meta.Offset
import Lean.Meta.AppBuilder
import Lean.Meta.KExprMap

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
  | add a b  => mkAdd (← toArith ctx a) (← toArith ctx b)
  | mulL k a => mkMul (mkNatLit k) (← toArith ctx a)
  | mulR a k => mkMul (← toArith ctx a) (mkNatLit k)

def LinearCnstr.toArith (ctx : Array Expr) (c : LinearCnstr) : MetaM Expr := do
  if c.eq then
    mkEq (← LinearExpr.toArith ctx c.lhs) (← LinearExpr.toArith ctx c.rhs)
  else
    return mkApp4 (mkConst ``LE.le [levelZero]) (mkConst ``Nat) (mkConst ``instLENat) (← LinearExpr.toArith ctx c.lhs) (← LinearExpr.toArith ctx c.rhs)

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
    match_expr e with
    | Nat.succ a => return inc (← toLinearExpr a)
    | Nat.add a b => return add (← toLinearExpr a) (← toLinearExpr b)
    | Nat.mul a b =>
      match (← evalNat a |>.run) with
      | some k => return mulL k (← toLinearExpr b)
      | none => match (← evalNat b |>.run) with
        | some k => return mulR (← toLinearExpr a) k
        | none => addAsVar e
    | _ =>
      let e ← instantiateMVarsIfMVarApp e
      let f := e.getAppFn
      if f.isConst && isNatProjInst f.constName! e.getAppNumArgs then
        let some e ← unfoldProjInst? e | addAsVar e
        toLinearExpr e
      else
        addAsVar e

partial def toLinearCnstr? (e : Expr) : M (Option LinearCnstr) := do
  let f := e.getAppFn
  match f with
  | Expr.mvar .. =>
    let eNew ← instantiateMVars e
    if eNew != e then
      toLinearCnstr? eNew
    else
      return none
  | Expr.const declName .. =>
    let numArgs := e.getAppNumArgs
    if declName == ``Eq && numArgs == 3 then
      return some { eq := true, lhs := (← toLinearExpr (e.getArg! 1)), rhs := (← toLinearExpr (e.getArg! 2)) }
    else if declName == ``Nat.le && numArgs == 2 then
      return some { eq := false, lhs := (← toLinearExpr (e.getArg! 0)), rhs := (← toLinearExpr (e.getArg! 1)) }
    else if declName == ``Nat.lt && numArgs == 2 then
      return some { eq := false, lhs := (← toLinearExpr (e.getArg! 0)).inc, rhs := (← toLinearExpr (e.getArg! 1)) }
    else if numArgs == 4 && (declName == ``GE.ge || declName == ``GT.gt) then
      if let some e ← unfoldDefinition? e then
        toLinearCnstr? e
      else
        return none
    else if numArgs == 4 && (declName == ``LE.le || declName == ``LT.lt) then
      if (← isDefEq (e.getArg! 0) (mkConst ``Nat)) then
        if let some e ← unfoldProjInst? e then
          toLinearCnstr? e
        else
          return none
      else
        return none
    else
      return none
  | _ => return none

def run (x : M α) : MetaM (α × Array Expr) := do
  let (a, s) ← x.run {}
  return (a, s.vars)

end ToLinear

export ToLinear (toLinearCnstr? toLinearExpr)

def toContextExpr (ctx : Array Expr) : MetaM Expr := do
  mkListLit (mkConst ``Nat) ctx.toList

def reflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)

namespace Lean.Meta.Linear.Nat
