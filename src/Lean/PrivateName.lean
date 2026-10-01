/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Notation
public import Init.Data.Option.Coe
import Init.SimpLemmas

public section

namespace Lean

/-! # Private name support.

   Suppose the user marks as declaration `n` as private. Then, we create
   the name: `_private.<module_name>.0 ++ n`.
   We say `_private.<module_name>.0` is the "private prefix"

   We assume that `<module_name>` is a valid user name and does not contain
   `Name.num` constructors. Thus, we can easily convert from
   private internal name to the user given name.
-/

def privateHeader : Name := `_private

/--
Constructs a private name from a module name `mainModule` without number components and
a user name `n`.
-/
def mkPrivateNameCore (mainModule : Name) (n : Name) : Name :=
  Name.num (privateHeader.appendCore mainModule) 0 |>.appendCore n

/--
Return `true` if `n` is of the form `_private.<module_name>.0`, or equivalently
of the form `mkPrivateNameCore moduleName .anonymous` with `moduleName.hasNum = false`.
-/
@[inline]
def isPrivatePrefix (n : Name) : Bool :=
  match n with
  | .num p 0 => go p
  | _ => false
where
  go (n : Name) : Bool :=
    n == privateHeader ||
    match n with
    | .str p _ => go p
    | _ => false

/--
Return `true` if `n` is a private name, that is, if `n` is equivalent to
`mkPrivateNameCore mainModule userName` with `mainModule.hasNum = false`.
-/
def isPrivateName (n : Name) : Bool :=
  match n with
  | .str p _ => isPrivateName p
  | .num p _ => isPrivatePrefix n || isPrivateName p
  | _        => false

private def privateToUserNameAux (n : Name) (h : isPrivateName n) : Name :=
  match hn : n with
  | .str p s => .str (privateToUserNameAux p h) s
  | .num p i => if h' : isPrivatePrefix n then .anonymous else .num (privateToUserNameAux p ?_) i
where finally simp_all [isPrivateName]

/--
Returns the user name corresponding to the private name `n` or `none` if `n` is not a private name.
-/
def privateToUserName? (n : Name) : Option Name :=
  if h : isPrivateName n then privateToUserNameAux n h
  else none

/--
Returns the user name corresponding to the private name `n` or `n` itself if `n` is not a
private name.
-/
def privateToUserName (n : Name) : Name :=
  if h : isPrivateName n then privateToUserNameAux n h
  else n

/--
If `n` is private name, returns `some pfx` such that `pfx.appendCore (privateToUserName n) = n`.
Otherwise, returns `none`.
-/
def privatePrefix? (n : Name) : Option Name :=
  match n with
  | .str p _ => privatePrefix? p
  | .num p _ => if isPrivatePrefix n then n else privatePrefix? p
  | _ => none

end Lean
