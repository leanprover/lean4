/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.FindExpr
import Lean.Declaration

namespace Lean

/-- Returns `true` if the expression is an application of `sorryAx`. -/
def Expr.isSorry (e : Expr) : Bool :=
  e.isAppOf ``sorryAx

/-- Returns `true` if the expression is of the form `sorryAx _ true ..`. -/
def Expr.isSyntheticSorry (e : Expr) : Bool :=
  e.isAppOf ``sorryAx && e.getAppNumArgs ≥ 2 && (e.getArg! 1).isConstOf ``Bool.true

/-- Returns `true` if the expression is of the form `sorryAx _ false ..`. -/
def Expr.isNonSyntheticSorry (e : Expr) : Bool :=
  e.isAppOf ``sorryAx && e.getAppNumArgs ≥ 2 && (e.getArg! 1).isConstOf ``Bool.false

def Expr.hasSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isConstOf ``sorryAx)

def Expr.hasSyntheticSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isSyntheticSorry)

def Expr.hasNonSyntheticSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isNonSyntheticSorry)

def Declaration.hasSorry (d : Declaration) : Bool := Id.run do
  d.foldExprM (fun r e => r || e.hasSorry) false

def Declaration.hasNonSyntheticSorry (d : Declaration) : Bool := Id.run do
  d.foldExprM (fun r e => r || e.hasNonSyntheticSorry) false

end Lean
