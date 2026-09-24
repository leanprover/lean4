/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Notation
public import Init.Data.Option.Coe
public import Init.Data.Option.Lemmas
import all Init.Meta.Defs

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

def mkPrivateNameCore (mainModule : Name) (n : Name) : Name :=
  Name.num (privateHeader.appendCore mainModule) 0 |>.appendCore n

/--
Return `true` if `n` is of the form `_private.<module_name>.0`
See comment above.
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

def privateToUserName? (n : Name) : Option Name :=
  if h : isPrivateName n then privateToUserNameAux n h
  else none

def privateToUserName (n : Name) : Name :=
  if h : isPrivateName n then privateToUserNameAux n h
  else n

def privatePrefix? (n : Name) : Option Name :=
  match n with
  | .str p _ => privatePrefix? p
  | .num p _ => if isPrivatePrefix n then n else privatePrefix? p
  | _ => none

attribute [local simp] Name.appendCore Name.hasNum

theorem Name.appendCore_eq_anonymous_iff {n n' : Name} :
    n.appendCore n' = anonymous ↔ n = anonymous ∧ n' = anonymous := by
  fun_induction appendCore with simp_all

theorem Name.appendCore_eq_right_iff {n n' : Name} :
    n.appendCore n' = n' ↔ n = anonymous := by
  fun_induction appendCore with simp_all

theorem isSome_privatePrefix? (n : Name) :
    (privatePrefix? n).isSome = isPrivateName n := by
  fun_induction privatePrefix? with simp_all [isPrivateName, isPrivatePrefix]

theorem isPrivatePrefix_of_privatePrefix?_eq_some {n : Name}
    (h : privatePrefix? n = some n') : isPrivatePrefix n' := by
  fun_induction privatePrefix? with simp_all

theorem appendCore_privatePrefix?_privateToUserName {n : Name} (h : isPrivateName n) :
    ((privatePrefix? n).get (by rwa [isSome_privatePrefix?])).appendCore (privateToUserName n) = n := by
  rw [privateToUserName, dite_eq_left h]
  fun_induction privateToUserNameAux with simp_all [privatePrefix?]

theorem isPrivateName_iff_privateToUserName_ne_self {n : Name} :
    isPrivateName n ↔ privateToUserName n ≠ n := by
  constructor
  · intro h h'
    have := appendCore_privatePrefix?_privateToUserName h
    rw [h', Name.appendCore_eq_right_iff] at this
    replace := isPrivatePrefix_of_privatePrefix?_eq_some
      (this ▸ Option.some_get (isSome_privatePrefix? _ ▸ h)).symm
    simp [isPrivatePrefix] at this
  · intro h
    rw [privateToUserName] at h
    split at h <;> simp_all

theorem isPrivateName_appendCore_right {n n' : Name} (h : isPrivateName n) :
    isPrivateName (n.appendCore n') := by
  induction n' with simp_all [isPrivateName]

private theorem isPrivatePrefix_go_implies_exists {n : Name} :
    isPrivatePrefix.go n → ∃ modNm, modNm.hasNum = false ∧ n = privateHeader.appendCore modNm := by
  induction n with
  | anonymous => simp [isPrivatePrefix.go, privateHeader]
  | str pre s ih =>
    simp only [isPrivatePrefix.go, Bool.or_eq_true, beq_iff_eq]
    rintro (h | h)
    · exists .anonymous
    · obtain ⟨modNm, h₁, h₂⟩ := ih h
      exists modNm.str s
      simp [*]
  | num => simp [isPrivatePrefix.go, privateHeader]

private theorem isPrivatePrefix_appendCore {modNm : Name} (h : modNm.hasNum = false) :
    isPrivatePrefix (privateHeader.appendCore modNm |>.num 0) := by
  rw [isPrivatePrefix]
  induction modNm with simp_all [isPrivatePrefix.go, privateHeader]

theorem isPrivateName_mkPrivateNameCore {modNm n : Name} (h : modNm.hasNum = false) :
    isPrivateName (mkPrivateNameCore modNm n) := by
  rw [mkPrivateNameCore]
  apply isPrivateName_appendCore_right
  rw [isPrivateName, Bool.or_eq_true]
  left
  exact isPrivatePrefix_appendCore h

theorem isPrivateName_iff_exists_mkPrivateNameCore {n : Name} :
    isPrivateName n ↔ ∃ modNm nm, modNm.hasNum = false ∧ n = mkPrivateNameCore modNm nm := by
  constructor
  · unfold mkPrivateNameCore
    induction n with
    | anonymous => simp [isPrivateName]
    | str _ s ih =>
      intro h
      rw [isPrivateName] at h
      obtain ⟨modNm, nm, h₁, rfl⟩ := ih h
      exists modNm, nm.str s
    | num p i ih =>
      rcases i with _ | i
      · simp only [isPrivateName, isPrivatePrefix, Bool.or_eq_true]
        rintro (h | h)
        · obtain ⟨modNm, hmodNm, rfl⟩ := isPrivatePrefix_go_implies_exists h
          exists modNm, .anonymous
        · obtain ⟨modNm, nm, h₁, rfl⟩ := ih h
          exists modNm, nm.num 0
      · simp only [isPrivateName, isPrivatePrefix, Bool.false_or]
        intro h
        obtain ⟨modNm, nm, h₁, rfl⟩ := ih h
        exists modNm, nm.num (i + 1)
  · rintro ⟨modNm, nm, h, rfl⟩
    exact isPrivateName_mkPrivateNameCore h

theorem isPrivateName_iff_exists_isPrivatePrefix {n : Name} :
    isPrivateName n ↔ ∃ pfx nm, isPrivatePrefix pfx ∧ n = pfx.appendCore nm := by
  rw [isPrivateName_iff_exists_mkPrivateNameCore]
  unfold mkPrivateNameCore
  constructor
  · rintro ⟨modNm, nm, h, rfl⟩
    exists privateHeader.appendCore modNm |>.num 0, nm
    simp [isPrivatePrefix_appendCore h]
  · rintro ⟨pfx, nm, h, rfl⟩
    revert h
    fun_cases isPrivatePrefix
    · intro h
      obtain ⟨modNm, h', rfl⟩ := isPrivatePrefix_go_implies_exists h
      exists modNm, nm, h'
    · simp

end Lean
