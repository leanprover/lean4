/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.ForEachExpr
import Lean.Elab.Command
import Lean.Meta.CollectFVars

/-!
# Name generator for declarations

This module provides functionality to generate a name for a declaration using its binders and its type.
This is used to generate names for anonymous instances.
-/

namespace Lean.Elab.Command

open Meta

/--
Generate a name for an instance with the given type.
Note that we elaborate the type twice. Once for producing the name, and another when elaborating the declaration.
-/
def mkInstanceName (binders : Array Syntax) (type : Syntax) : CommandElabM Name := do
  let savedState ← get
  try
    let result ← runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => Term.withoutErrToSorry do
      let type ← instantiateMVars (← Term.elabType type)
      let ref ← IO.mkRef ""
      Meta.forEachExpr type fun e => do
        if e.isForall then ref.modify (· ++ "ForAll")
        else if e.isProp then ref.modify (· ++ "Prop")
        else if e.isType then ref.modify (· ++ "Type")
        else if e.isSort then ref.modify (· ++ "Sort")
        else if e.isConst then
          match e.constName!.eraseMacroScopes with
          | .str _ str =>
              if str.front.isLower then
                ref.modify (· ++ str.capitalize)
              else
                ref.modify (· ++ str)
          | _ => pure ()
      ref.get
    set savedState
    liftMacroM <| mkUnusedBaseName <| Name.mkSimple ("inst" ++ result)
  catch _ =>
    set savedState
    liftMacroM <| mkUnusedBaseName <| Name.mkSimple "instance"
