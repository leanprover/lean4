/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Ext
public import Lean.Meta.Tactic.Grind.Extension
public section
namespace Lean.Meta.Grind
/-! Grind extensionality attribute to mark which `[ext]` theorems should be used. -/

def validateExtAttr (declName : Name) : CoreM Unit := do
  if !(← Ext.isExtTheorem declName) then
  if !(isStructure (← getEnv) declName) then
    throwError "invalid `[grind ext]`, `{.ofConstName declName}` is neither tagged with `[ext]` nor is a structure"

def ExtTheorems.eraseDecl (s : ExtTheorems) (declName : Name) : CoreM ExtTheorems := do
  if s.contains declName then
    return s.erase declName
  else
    throwError "`{.ofConstName declName}` is not marked with the `[grind ext]` attribute"

end Lean.Meta.Grind
