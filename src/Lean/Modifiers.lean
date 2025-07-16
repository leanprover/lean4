/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.EnvExtension
import Lean.PrivateName

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

def isPrivateNameFromImportedModule (env : Environment) (n : Name) : Bool :=
  if env.header.isModule then
    -- Allow access through `import all`.
    -- TODO: this should not be relevant as soon as we make sure we never export any kind of private
    -- constant.
    !env.contains n && (env.setExporting false).contains n
  else match privateToUserName? n with
    | some userName => mkPrivateName env userName != n
    | _ => false

end Lean
