/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean

builtin_initialize protectedExt : TagDeclarationExtension ← mkTagDeclarationExtension `protected

@[export lean_add_protected]
def addProtected (env : Environment) (n : Name) : Environment :=
  protectedExt.tag env n

@[export lean_is_protected]
def isProtected (env : Environment) (n : Name) : Bool :=
  protectedExt.isTagged env n

/- Private name support.

   Suppose the user marks as declaration `n` as private. Then, we create
   the name: `_private.<module_name>.0 ++ n`.
   We say `_private.<module_name>.0` is the "private prefix"

   We assume that `n` is a valid user name and does not contain
   `Name.num` constructors. Thus, we can easily convert from
   private internal name to the user given name.
-/

def privateHeader : Name := `_private

def mkPrivateName (env : Environment) (n : Name) : Name :=
  Name.mkNum (privateHeader ++ env.mainModule) 0 ++ n

def isPrivateName : Name → Bool
  | n@(Name.str p _ _) => n == privateHeader || isPrivateName p
  | Name.num p _ _     => isPrivateName p
  | _                  => false

@[export lean_is_private_name]
def isPrivateNameExport (n : Name) : Bool :=
  isPrivateName n

private def privateToUserNameAux : Name → Name
  | Name.str p s _ => Name.mkStr (privateToUserNameAux p) s
  | _              => Name.anonymous

@[export lean_private_to_user_name]
def privateToUserName? (n : Name) : Option Name :=
  if isPrivateName n then privateToUserNameAux n
  else none

def isPrivateNameFromImportedModule (env : Environment) (n : Name) : Bool :=
  match privateToUserName? n with
  | some userName => mkPrivateName env userName != n
  | _ => false

private def privatePrefixAux : Name → Name
  | Name.str p _ _ => privatePrefixAux p
  | n              => n

@[export lean_private_prefix]
def privatePrefix? (n : Name) : Option Name :=
  if isPrivateName n then privatePrefixAux n
  else none

end Lean
