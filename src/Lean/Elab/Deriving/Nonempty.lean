/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

prelude
public import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

public section

namespace Lean.Elab
open Command Meta Parser Term

private def mkNonemptyInstance (declName : Name) : TermElabM Syntax.Command := do
  let ctx ← Deriving.mkContext "nonempty" declName
  let indVal ← getConstInfoInduct declName
  forallTelescopeReducing indVal.type fun paramsIndices _ => do
  let mut indArgs := #[]
  let mut binders := #[]
  for x in paramsIndices do
    let arg := mkIdent (← mkFreshUserName (← x.fvarId!.getUserName).eraseMacroScopes)
    indArgs := indArgs.push arg
    binders := binders.push (← `(bracketedBinderF| {$arg}))
    if let .sort u ← whnf (← inferType x) then
      if let .some _ ← decLevel? u then
        binders := binders.push (← `(bracketedBinderF| [Nonempty $arg]))
  let ctorTacs ← indVal.ctors.toArray.mapM fun ctor =>
    `(tactic| apply @$(mkCIdent ctor) <;> exact Classical.ofNonempty)
  let vis := ctx.mkVisibilityFromTypes
  let expAttr := ctx.mkExposeAttrFromCtors
  `(command| variable $binders* in
    @[$expAttr] $vis:visibility instance : Nonempty (@$(mkCIdent declName) $indArgs*) :=
      by constructor; first $[| $ctorTacs:tactic]*)

def mkNonemptyInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkNonemptyInstance declName)
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `Nonempty mkNonemptyInstanceHandler

end Lean.Elab
