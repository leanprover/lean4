/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean

builtin_initialize protectedExt : TagDeclarationExtension ← mkTagDeclarationExtension

@[export lean_add_protected]
def addProtected (env : Environment) (n : Name) : Environment :=
  protectedExt.tag env n

@[export lean_is_protected]
def isProtected (env : Environment) (n : Name) : Bool :=
  protectedExt.isTagged env n

/-!
# Private name support.

We use a reserved macro scope to encode private names.
-/

def mkPrivateName (env : Environment) (n : Name) : Name :=
  if n.hasMacroScopes then
    let view := extractMacroScopes n
    { view with scopes := privateMacroScope :: view.scopes.erase privateMacroScope }.review
  else
    addMacroScope env.mainModule n privateMacroScope

def isPrivateName (declName : Name) : Bool :=
  if declName.hasMacroScopes then
    let view := extractMacroScopes declName
    view.scopes.contains privateMacroScope
  else
    false

@[export lean_is_private_name]
def isPrivateNameExport (n : Name) : Bool :=
  isPrivateName n

@[export lean_private_to_user_name]
def privateToUserName? (n : Name) : Option Name :=
  if n.hasMacroScopes then
    let view := extractMacroScopes n
    if view.scopes.contains privateMacroScope then
      { view with scopes := view.scopes.erase privateMacroScope }.review
    else
      none
  else
    none

def isPrivateNameFromImportedModule (env : Environment) (n : Name) : Bool :=
  if n.hasMacroScopes then
    let view := extractMacroScopes n
    if view.scopes.contains privateMacroScope then
      view.imported == env.mainModule
    else
      false
  else
    false

end Lean
