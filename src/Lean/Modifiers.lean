/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.EnvExtension

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

end Lean
