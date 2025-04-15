/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Notation

namespace Lean

/-! # Private name support.

   Suppose the user marks as declaration `n` as private. Then, we create
   the name: `_private.<module_name>.0 ++ n`.
   We say `_private.<module_name>.0` is the "private prefix"

   We assume that `n` is a valid user name and does not contain
   `Name.num` constructors. Thus, we can easily convert from
   private internal name to the user given name.
-/

def privateHeader : Name := `_private

def mkPrivateNameCore (mainModule : Name) (n : Name) : Name :=
  Name.mkNum (privateHeader ++ mainModule) 0 ++ n

def isPrivateName : Name → Bool
  | n@(.str p _) => n == privateHeader || isPrivateName p
  | .num p _     => isPrivateName p
  | _            => false

@[export lean_is_private_name]
def isPrivateNameExport (n : Name) : Bool :=
  isPrivateName n

/--
Return `true` if `n` is of the form `_private.<module_name>.0`
See comment above.
-/
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

private def privateToUserNameAux (n : Name) : Name :=
  match n with
  | .str p s => .str (privateToUserNameAux p) s
  | .num p i => if isPrivatePrefix n then .anonymous else .num (privateToUserNameAux p) i
  | _        => .anonymous

@[export lean_private_to_user_name]
def privateToUserName? (n : Name) : Option Name :=
  if isPrivateName n then privateToUserNameAux n
  else none

def privateToUserName (n : Name) : Name :=
  if isPrivateName n then privateToUserNameAux n
  else n

private def privatePrefixAux : Name → Name
  | .str p _ => privatePrefixAux p
  | n        => n

@[export lean_private_prefix]
def privatePrefix? (n : Name) : Option Name :=
  if isPrivateName n then privatePrefixAux n
  else none

end Lean
