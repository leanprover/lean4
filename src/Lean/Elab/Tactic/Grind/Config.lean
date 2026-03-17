/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.ConfigSetter
public section
namespace Lean.Elab.Tactic.Grind

/-- Sets a field of the `grind` configuration object. -/
declare_config_getter setConfigField Grind.Config

def elabConfigItems (init : Grind.Config) (items : Array (TSyntax `Lean.Parser.Tactic.configItem))
    : TermElabM Grind.Config := do
  let mut config := init
  for item in items do
    match item with
    | `(Lean.Parser.Tactic.configItem| ($fieldName:ident := true))
    | `(Lean.Parser.Tactic.configItem| +$fieldName:ident) =>
      config ← withRef fieldName <| setConfigField config fieldName.getId true
    | `(Lean.Parser.Tactic.configItem| ($fieldName:ident := false))
    | `(Lean.Parser.Tactic.configItem| -$fieldName:ident) =>
      config ← withRef fieldName <| setConfigField config fieldName.getId false
    | `(Lean.Parser.Tactic.configItem| ($fieldName:ident := $val:num)) =>
      config ← withRef fieldName <| setConfigField config fieldName.getId (.ofNat val.getNat)
    | _ => throwErrorAt item "unexpected configuration option"
  return config

def withConfigItems (items : Array (TSyntax `Lean.Parser.Tactic.configItem))
    (k : GrindTacticM α) : GrindTacticM α := do
  if items.isEmpty then
    k
  else
    let config := (← read).ctx.config
    let config ← elabConfigItems config items
    withReader (fun c => { c with ctx.config := config }) do k

end Lean.Elab.Tactic.Grind
