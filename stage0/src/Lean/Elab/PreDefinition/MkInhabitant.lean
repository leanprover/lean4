/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
namespace Lean.Elab
open Meta

private def mkInhabitant? (type : Expr) : MetaM (Option Expr) := do
  try
    pure $ some (← mkArbitrary type)
  catch _ =>
    pure none

private def findAssumption? (xs : Array Expr) (type : Expr) : MetaM (Option Expr) := do
  xs.findM? fun x => do isDefEq (← inferType x) type

private def mkFnInhabitant? (xs : Array Expr) (type : Expr) : MetaM (Option Expr) :=
  let rec loop
    | 0,   type => mkInhabitant? type
    | i+1, type => do
      let x := xs[i]
      let type ← mkForallFVars #[x] type;
      match (← mkInhabitant? type) with
      | none     => loop i type
      | some val => pure $ some (← mkLambdaFVars xs[0:i] val)
  loop xs.size type

/- TODO: add a global IO.Ref to let users customize/extend this procedure -/

def mkInhabitantFor (declName : Name) (xs : Array Expr) (type : Expr) : MetaM Expr := do
  match (← mkInhabitant? type) with
  | some val => mkLambdaFVars xs val
  | none     =>
  match (← findAssumption? xs type) with
  | some x => mkLambdaFVars xs x
  | none   =>
  match (← mkFnInhabitant? xs type) with
  | some val => pure val
  | none => throwError "failed to compile partial definition '{declName}', failed to show that type is inhabited"

end Lean.Elab
