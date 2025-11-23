/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.ScopedEnvExtension
public section
namespace Lean.Meta.Grind

private builtin_initialize funCCExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun s declName => s.insert declName
  }

def getFunCCSet : CoreM NameSet :=
  return funCCExt.getState (← getEnv)

def hasFunCCAttr (declName : Name) : CoreM Bool := do
  return (← getFunCCSet).contains declName

def addFunCCAttr (declName : Name) (attrKind : AttributeKind) : CoreM Unit := do
  funCCExt.add declName attrKind

def eraseFunCCAttr (declName : Name) : CoreM Unit := do
  let s ← getFunCCSet
  unless s.contains declName do
    throwError "`{.ofConstName declName}` is not marked with the `[grind]` attribute"
  let s := s.erase declName
  modifyEnv fun env => funCCExt.modifyState env fun _ => s

end Lean.Meta.Grind
