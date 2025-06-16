/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Ext

namespace Lean.Meta.Grind
/-! Grind extensionality attribute to mark which `[ext]` theorems should be used. -/

/-- Extensionality theorems that can be used by `grind` -/
abbrev ExtTheorems := PHashSet Name

builtin_initialize extTheoremsExt : SimpleScopedEnvExtension Name ExtTheorems ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun s declName => s.insert declName
  }

def validateExtAttr (declName : Name) : CoreM Unit := do
  unless (← Ext.isExtTheorem declName) do
    throwError "invalid `[grind ext]`, `{declName}` is not tagged with `[ext]`"

def addExtAttr (declName : Name) (attrKind : AttributeKind) : CoreM Unit := do
  validateExtAttr declName
  extTheoremsExt.add declName attrKind

private def eraseDecl (s : ExtTheorems) (declName : Name) : CoreM ExtTheorems := do
  if s.contains declName then
    return s.erase declName
  else
    throwError "`{declName}` is not marked with the `[grind ext]` attribute"

def eraseExtAttr (declName : Name) : CoreM Unit := do
  let s := extTheoremsExt.getState (← getEnv)
  let s ← eraseDecl s declName
  modifyEnv fun env => extTheoremsExt.modifyState env fun _ => s

def isExtTheorem (declName : Name) : CoreM Bool := do
  return extTheoremsExt.getState (← getEnv) |>.contains declName

end Lean.Meta.Grind
