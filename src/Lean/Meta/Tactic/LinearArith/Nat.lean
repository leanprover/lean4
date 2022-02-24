/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Check
import Lean.Meta.Offset

namespace Lean.Meta.Linear.Nat

deriving instance Repr for Nat.Linear.Expr

abbrev LinearExpr  := Nat.Linear.Expr
abbrev LinearCnstr := Nat.Linear.ExprCnstr

def LinearExpr.toExpr (ctx : Array Expr) (e : LinearExpr) : Expr :=
  open Nat.Linear.Expr in
  match e with
  | num v    => mkApp (mkConst ``num) (mkNatLit v)
  | var i    => if h : i < ctx.size then ctx.get ⟨i, h⟩ else mkApp (mkConst ``var) (mkNatLit i)
  | add a b  => mkApp2 (mkConst ``add) (toExpr ctx a) (toExpr ctx b)
  | mulL k a => mkApp2 (mkConst ``mulL) (mkNatLit k) (toExpr ctx a)
  | mulR a k => mkApp2 (mkConst ``mulL) (toExpr ctx a) (mkNatLit k)

instance : ToExpr LinearExpr where
  toExpr a := a.toExpr #[]
  toTypeExpr := mkConst ``Nat.Linear.Expr

namespace ToLinear

structure State where
  varMap : ExprMap Nat
  vars   : Array Expr

abbrev M := StateRefT State MetaM

open Nat.Linear.Expr

def addAsVar (e : Expr) : M LinearExpr := do
  if let some x := (← get).varMap.find? e then
    return var x
  else
    let x := (← get).vars.size
    modify fun s => { varMap := s.varMap.insert e x, vars := s.vars.push e }
    return var x

partial def toLinearExpr (e : Expr) : M LinearExpr := do
  match e with
  | Expr.lit (Literal.natVal n) _ => return num n
  | Expr.mdata _ e _              => toLinearExpr e
  | Expr.const ``Nat.zero ..      => return num 0
  | Expr.app ..                   => visit e
  | Expr.mvar ..                  => visit e
  | _                             => addAsVar e
where
  visit (e : Expr) : M LinearExpr := do
    let f := e.getAppFn
    match f with
    | Expr.mvar .. =>
      let eNew ← instantiateMVars e
      if eNew != e then
        toLinearExpr eNew
      else
        addAsVar e
    | Expr.const declName .. =>
      let numArgs := e.getAppNumArgs
      if declName == ``Nat.succ && numArgs == 1 then
        return inc (← toLinearExpr e.appArg!)
      else if declName == ``Nat.add && numArgs == 2 then
        return add (← toLinearExpr (e.getArg! 0)) (← toLinearExpr (e.getArg! 1))
      else if declName == ``Nat.mul && numArgs == 2 then
        match (← evalNat (e.getArg! 0) |>.run) with
        | some k => return mulL k (← toLinearExpr (e.getArg! 1))
        | none => match (← evalNat (e.getArg! 1) |>.run) with
          | some k => return mulR (← toLinearExpr (e.getArg! 0)) k
          | none => addAsVar e
      else if isNatProjInst declName numArgs then
        if let some e ← unfoldProjInst? e then
          toLinearExpr e
        else
          addAsVar e
      else
        addAsVar e
    | _ => addAsVar e

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
    else if numArgs == 4 && (declName == ``LE.le || declName == ``GE.ge || declName == ``LT.lt || declName == ``GT.gt) then
      if let some e ← unfoldProjInst? e then
        toLinearCnstr? e
      else
        return none
    else
      return none
  | _ => return none

end ToLinear

end Lean.Meta.Linear.Nat
