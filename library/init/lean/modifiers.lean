/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean

def mkProtectedExtension : IO (PersistentEnvExtension Name NameSet) :=
registerPersistentEnvExtension {
  name       := `protected,
  initState  := {},
  addEntryFn := λ init s n, if init then s else s.insert n,
  toArrayFn  := λ es, es.toArray.qsort Name.quickLt,
  lazy       := false }

@[init mkProtectedExtension]
constant protectedExt : PersistentEnvExtension Name NameSet := default _

@[export lean.add_protected_core]
def addProtected (env : Environment) (n : Name) : Environment :=
protectedExt.addEntry env n

@[export lean.is_protected_core]
def isProtected (env : Environment) (n : Name) : Bool :=
match env.getModuleIdxFor n with
| some modIdx := (protectedExt.getModuleEntries env modIdx).binSearchContains n Name.quickLt
| none        := (protectedExt.getState env).contains n

def mkPrivateExtension : IO (EnvExtension Nat) :=
registerEnvExtension 1

@[init mkPrivateExtension]
constant privateExt : EnvExtension Nat := default _

/- Private name support.

   Suppose the user marks as declaration `n` as private. Then, we create
   the name: `_private.<module_name>.<index> ++ n`.
   We say `_private.<module_name>.<index>` is the "private prefix"
   where `<index>` comes from the environment extension `privateExt`.

   We assume that `n` is a valid user name and does not contain
   `Name.mkNumeral` constructors. Thus, we can easily convert from
   private internal name to user given name.
-/

def privateHeader : Name := `_private

@[export lean.mk_private_prefix_core]
def mkPrivatePrefix (env : Environment) : Environment × Name :=
let idx := privateExt.getState env in
let p   := Name.mkNumeral (privateHeader ++ env.mainModule) idx in
let env := privateExt.setState env (idx+1) in
(env, p)

@[export lean.mk_private_name_core]
def mkPrivateName (env : Environment) (n : Name) : Environment × Name :=
let (env, p) := mkPrivatePrefix env in
(env, p ++ n)

def isPrivateName : Name → Bool
| n@(Name.mkString p _) := n == privateHeader || isPrivateName p
| (Name.mkNumeral p _)  := isPrivateName p
| _                     := false

@[export lean.is_private_name_core]
def isPrivateNameExport (n : Name) : Bool :=
isPrivateName n

private def privateToUserNameAux : Name → Name
| (Name.mkString p s)  := Name.mkString (privateToUserNameAux p) s
| _                    := Name.anonymous

@[export lean.private_to_user_name_core]
def privateToUserName (n : Name) : Option Name :=
if isPrivateName n then privateToUserNameAux n
else none

private def privatePrefixAux : Name → Name
| (Name.mkString p _) := privatePrefixAux p
| n                   := n

@[export lean.private_prefix_core]
def privatePrefix (n : Name) : Option Name :=
if isPrivateName n then privatePrefixAux n
else none

end Lean
