/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.PrettyPrinter
namespace Lean.Elab
open Meta

private def mkInhabitant? (type : Expr) (useOfNonempty : Bool) : MetaM (Option Expr) := do
  try
    if useOfNonempty then
      return some (← mkOfNonempty type)
    else
      return some (← mkDefault type)
  catch _ =>
    return none

private def findAssumption? (xs : Array Expr) (type : Expr) : MetaM (Option Expr) := do
  xs.findM? fun x => do isDefEq (← inferType x) type

private def mkFnInhabitant? (xs : Array Expr) (type : Expr) (useOfNonempty : Bool) : MetaM (Option Expr) :=
  let rec loop
    | 0,   type => mkInhabitant? type useOfNonempty
    | i+1, type => do
      let x := xs[i]!
      let type ← mkForallFVars #[x] type;
      match (← mkInhabitant? type useOfNonempty) with
      | none     => loop i type
      | some val => return some (← mkLambdaFVars xs[0:i] val)
  loop xs.size type

/--
Find an inhabitant while doing delta unfolding.
-/
private partial def mkInhabitantForAux? (xs : Array Expr) (type : Expr) (useOfNonempty : Bool) : MetaM (Option Expr) := withIncRecDepth do
  if let some val ← mkInhabitant? type useOfNonempty <||> findAssumption? xs type then
    mkLambdaFVars xs val
  else if let some val ← mkFnInhabitant? xs type useOfNonempty then
    return val
  else
    let type ← whnfCore type
    if type.isForall then
      forallTelescope type fun xs' type' => do
        mkInhabitantForAux? (xs ++ xs') type' useOfNonempty
    else if let some type' ← unfoldDefinition? type then
      mkInhabitantForAux? xs type' useOfNonempty
    else
      return none

/- TODO: add a global IO.Ref to let users customize/extend this procedure -/
def mkInhabitantFor (declName : Name) (xs : Array Expr) (type : Expr) : MetaM Expr := do
  if let some val ← mkInhabitantForAux? xs type false <||> mkInhabitantForAux? xs type true then
    return val
  else
    throwError "\
      failed to compile 'partial' definition '{declName}', could not prove that the type\
      {indentExpr (← mkForallFVars xs type)}\n\
      is nonempty.\n\
      \n\
      This process uses multiple strategies:\n\
      - It looks for a parameter that matches the return type.\n\
      - It tries synthesizing '{MessageData.ofConstName ``Inhabited}' and '{MessageData.ofConstName ``Nonempty}' \
        instances for the return type.\n\
      - It tries unfolding the return type.\n\
      \n\
      If the return type is defined using the 'structure' or 'inductive' command, \
      you can try adding a 'deriving Nonempty' clause to it."

end Lean.Elab
