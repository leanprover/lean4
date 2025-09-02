/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.ScopedEnvExtension

public section

namespace Lean.Meta

builtin_initialize globalInstanceExtension : SimpleScopedEnvExtension Name (PersistentHashMap Name Unit)  ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun s n => s.insert n ()
  }

def addGlobalInstance (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  globalInstanceExtension.add declName attrKind

@[export lean_is_instance]
def isGlobalInstance (env : Environment) (declName : Name) : Bool :=
  globalInstanceExtension.getState env |>.contains declName

end Lean.Meta
