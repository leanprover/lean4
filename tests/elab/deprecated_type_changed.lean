module

/-!
Tests warnings for missing and unnecessary type-change markers in `@[deprecated]` attributes.
-/

set_option linter.deprecated true

def newDecl : Nat := 0

/--
warning: The updated constant has a different type:
  Nat
instead of
  Bool

This suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often excepected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.

If the type difference is intentional, use `+typeChanged` to silence this warning.

Hint: Add `+typeChanged`:
  [apply] +typeChanged
-/
#guard_msgs in
@[deprecated newDecl (since := "2026-07-27")]
def oldDecl : Bool := false

abbrev MyNat := Nat

def reduciblyDefEqNew : MyNat := 0

#guard_msgs in
@[deprecated reduciblyDefEqNew (since := "2026-07-27")]
def reduciblyDefEqOld : Nat := 0

universe u

def universeParamNew {α : Type u} (x : α) : α := x

#guard_msgs in
@[deprecated universeParamNew (since := "2026-07-29")]
def universeParamOld := @universeParamNew

/-- warning: `universeParamOld` has been deprecated: Use `universeParamNew` instead -/
#guard_msgs in
example {α : Type u} (x : α) : α := universeParamOld x

#guard_msgs in
@[deprecated newDecl +typeChanged (since := "2026-07-27")]
def typeChangedShort : Bool := false

#guard_msgs in
@[deprecated newDecl (typeChanged := true) (since := "2026-07-27")]
def typeChangedLong : Bool := false

/--
warning: The `+typeChanged` marker is not needed because the updated constant has the same type.
-/
#guard_msgs in
@[deprecated reduciblyDefEqNew +typeChanged (since := "2026-07-30")]
def unnecessaryTypeChangedShort : Nat := 0

/--
warning: The `+typeChanged` marker is not needed because the updated constant has the same type.
-/
#guard_msgs in
@[deprecated reduciblyDefEqNew (typeChanged := true) (since := "2026-07-30")]
def unnecessaryTypeChangedLong : Nat := 0
