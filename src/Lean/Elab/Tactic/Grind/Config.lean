/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.CoreM
meta import Lean.Elab.Tactic.ConfigSetter
public section
namespace Lean.Elab.Tactic.Grind

/-- Sets a field of the `grind` configuration object. -/
declare_config_getter setConfigField Grind.Config

def elabConfigItems (init : Grind.Config) (items : Array (TSyntax `Lean.Parser.Tactic.configItem))
    : CoreM Grind.Config := do
  let mut config := init
  for item in items do
    match item with
    | `(Lean.Parser.Tactic.configItem| ($fieldName:ident := true))
    | `(Lean.Parser.Tactic.configItem| +$fieldName:ident) =>
      config ← setConfigField config fieldName.getId true
    | `(Lean.Parser.Tactic.configItem| ($fieldName:ident := false))
    | `(Lean.Parser.Tactic.configItem| -$fieldName:ident) =>
      config ← setConfigField config fieldName.getId false
    | `(Lean.Parser.Tactic.configItem| ($fieldName:ident := $val:num)) =>
      config ← setConfigField config fieldName.getId (.ofNat val.getNat)
    | _ => throwErrorAt item "unexpected configuration option"
  return config

end Lean.Elab.Tactic.Grind
