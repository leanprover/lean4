/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.PrivateName

namespace Lean

builtin_initialize protectedExt : TagDeclarationExtension ← mkTagDeclarationExtension

def addProtected (env : Environment) (n : Name) : Environment :=
  protectedExt.tag env n

def isProtected (env : Environment) (n : Name) : Bool :=
  protectedExt.isTagged env n

def mkPrivateName (env : Environment) (n : Name) : Name :=
  Name.mkNum (privateHeader ++ env.mainModule) 0 ++ n

def isPrivateNameFromImportedModule (env : Environment) (n : Name) : Bool :=
  match privateToUserName? n with
  | some userName => mkPrivateName env userName != n
  | _ => false

end Lean
