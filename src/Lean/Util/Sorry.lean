/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindExpr
import Lean.Declaration

namespace Lean

def Expr.isSorry : Expr → Bool
  | app (app (.const ``sorryAx ..) ..) .. => true
  | _ => false

def Expr.isSyntheticSorry : Expr → Bool
  | app (app (const ``sorryAx ..) ..) (const ``Bool.true ..) => true
  | _ => false

def Expr.isNonSyntheticSorry : Expr → Bool
  | app (app (const ``sorryAx ..) ..) (const ``Bool.false ..) => true
  | _ => false

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
