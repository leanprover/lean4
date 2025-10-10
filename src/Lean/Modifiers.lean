/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.EnvExtension
public import Lean.PrivateName

public section

namespace Lean

builtin_initialize protectedExt : TagDeclarationExtension ← mkTagDeclarationExtension

def addProtected (env : Environment) (n : Name) : Environment :=
  protectedExt.tag env n

def isProtected (env : Environment) (n : Name) : Bool :=
  protectedExt.isTagged env n

def mkPrivateName (env : Environment) (n : Name) : Name :=
  -- If name is already private, remove previous suffix first. We need to ensure the resulting name
  -- is private to *this* module.
  mkPrivateNameCore env.mainModule <| privateToUserName n

def isInaccessiblePrivateName (env : Environment) (n : Name) : Bool := Id.run do
  if !isPrivateName n then
    return false
  -- All private names are inaccessible from the public scope
  if env.isExporting then
    return true
  -- In the private scope, ...
  match env.getModuleIdxFor? n with
  | some modIdx =>
    -- ... allow access through `import all`
    !env.header.isModule || !env.header.modules[modIdx]?.any (·.importAll)
  | none =>
    -- ... allow all accesses in the current module
    false

end Lean
