/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.NotationExtra

namespace Lean.Grind
/-!
This is a hackish module for hovering node information in the `grind` tactic state.
-/

inductive NodeDef where
  | unit

set_option linter.unusedVariables false in
def node_def (_ : Nat) {α : Sort u} {a : α} : NodeDef := .unit

@[app_unexpander node_def]
meta def nodeDefUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $id:num) => return mkIdent <| Name.mkSimple $ "#" ++ toString id.getNat
  | _ => throw ()

@[app_unexpander NodeDef]
meta def NodeDefUnexpander : PrettyPrinter.Unexpander := fun _ => do
  return mkIdent <| Name.mkSimple "NodeDef"

end Lean.Grind
