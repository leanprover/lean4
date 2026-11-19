/-!
Tests that the commands in front of `in` do not report deprecated declarations when the command
after `in` is a deprecated declaration, just like the body of the deprecated declaration.
-/

set_option linter.deprecated true
set_option warn.classDefReducibility false

class C where
  x : Nat

class D where
  z : Nat

@[deprecated "no replacement" (since := "2025-01-01")] def deprecatedInst : C := ⟨1⟩

@[deprecated "no replacement" (since := "2025-01-01")] class DeprecatedClass (α : Type) where
  y : α

namespace NS
@[deprecated "no replacement" (since := "2025-01-01")] def deprecatedDef : Nat := 1
end NS

#guard_msgs in
attribute [local instance] deprecatedInst in
@[deprecated "no replacement" (since := "2025-01-01")] def usesInst : Nat := C.x

#guard_msgs in
attribute [local instance] deprecatedInst in
@[deprecated "no replacement" (since := "2025-01-01")] instance usesInstInst : D := ⟨C.x⟩

#guard_msgs in
attribute [local instance] deprecatedInst in
@[deprecated "no replacement" (since := "2025-01-01")] theorem usesInstThm : C.x = 1 := rfl

#guard_msgs in
variable {α : Type} [DeprecatedClass α] in
@[deprecated "no replacement" (since := "2025-01-01")] def usesClass : α := DeprecatedClass.y

#guard_msgs in
open NS (deprecatedDef) in
@[deprecated "no replacement" (since := "2025-01-01")] def usesOpen : Nat := deprecatedDef

/-! Nested `in` commands in front of a deprecated declaration. -/

#guard_msgs in
attribute [local instance] deprecatedInst in
open NS (deprecatedDef) in
@[deprecated "no replacement" (since := "2025-01-01")] def nested₁ : Nat := C.x + deprecatedDef

#guard_msgs in
set_option pp.all true in
attribute [local instance] deprecatedInst in
@[deprecated "no replacement" (since := "2025-01-01")] def nested₂ : Nat := C.x

/-! The local instance is only active for the declaration after `in`. -/

/--
error: failed to synthesize instance of type class
  C

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
@[deprecated "no replacement" (since := "2025-01-01")] def afterwards : Nat := C.x

/-! Commands in front of a declaration that is not deprecated still report deprecations. -/

/-- warning: `deprecatedInst` has been deprecated: no replacement -/
#guard_msgs in
attribute [local instance] deprecatedInst in
def notDeprecated : Nat := C.x

/--
warning: `deprecatedInst` has been deprecated: no replacement
---
warning: `NS.deprecatedDef` has been deprecated: no replacement
-/
#guard_msgs in
attribute [local instance] deprecatedInst in
open NS (deprecatedDef) in
def notDeprecatedNested : Nat := C.x

/-- warning: `deprecatedInst` has been deprecated: no replacement -/
#guard_msgs in
attribute [local instance] deprecatedInst in
example : Nat := C.x

/-! Only the attribute on the declaration itself counts, not on one in its body. -/

/-- warning: `deprecatedInst` has been deprecated: no replacement -/
#guard_msgs in
attribute [local instance] deprecatedInst in
def withLetRec : Nat := go
where
  @[deprecated "no replacement" (since := "2025-01-01")] go : Nat := C.x
