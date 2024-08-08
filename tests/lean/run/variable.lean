/-! # Basic section variable tests -/

/-! Directly referenced variables should be included. -/
variable {n : Nat} in
theorem t1 : n = n := by induction n <;> rfl

/-! Variables mentioned only in the body should not be included. -/
variable {n : Nat} in
/-- error: unknown identifier 'n' -/
#guard_msgs in
theorem t2 : ∃ (n : Nat), n = n := by exists n

/-! Variables transitively mentioned should be included. -/
variable {n : Nat} (h : n = n) in
theorem t3 : h = h := rfl

/-! Instance variables mentioning only included variables should be included. -/
variable {α : Type} [ToString α] in
theorem t4 (a : α) : a = a := let _ := toString a; rfl

/-! Instance variables not mentioning only included variables should not be included. -/
variable {α β : Type} [Coe α β] in
/--
error: don't know how to synthesize placeholder
context:
α : Type
a : α
⊢ a = a
-/
#guard_msgs in
theorem t5 (a : α) : a = a := _

/-! Accidentally included variables should be warned for. -/
variable {α : Type} [ToString α] in
/-- warning: included section variable '[ToString α]' is not used in 't6', consider excluding it -/
#guard_msgs in
theorem t6 (a : α) : a = a := rfl

/-! `include` should always include. -/
variable {n : Nat} in
include n in
theorem t7 : ∃ (n : Nat), n = n := by exists n

/-! traversal order bug broke instance inclusion -/
variable {M N : Type} (r : N → N → Prop)
class IsTrans (N : Type) (r : N → N → Prop) : Prop
variable [IsTrans N r] {a b c d : N}
/--
warning: included section variable '[IsTrans N r]' is not used in 'act_rel_of_rel_of_act_rel', consider excluding it
-/
#guard_msgs in
theorem act_rel_of_rel_of_act_rel (ab : r a b) : r a b := ab

/-! More complex include case, instance should be included via `f`. -/
class EquivLike (F : Type) (α β : Type) : Type
variable {F : Type} [EquivLike F α β] (f : F) in
include f in
theorem MulEquiv.decompositionMonoid (_b : β) : α = α :=
  let _ : EquivLike F α β := inferInstance; let _ := f; rfl
/-- info: MulEquiv.decompositionMonoid {α β F : Type} [EquivLike F α β] (f : F) (_b : β) : α = α -/
#guard_msgs in
#check MulEquiv.decompositionMonoid

section
/-! `omit` -/
variable [ToString α] [ToString β]

/--
error: failed to synthesize
  ToString α
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
omit [ToString α] in
theorem t8 (a : α) (b : β) : True :=
  let _ := toString a; let _ := toString b; trivial

/--
error: failed to synthesize
  ToString β
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
omit [ToString β] in
theorem t9 (a : α) (b : β) : True :=
  let _ := toString a; let _ := toString b; trivial

/--
error: failed to synthesize
  ToString α
use `set_option diagnostics true` to get diagnostic information
---
error: failed to synthesize
  ToString β
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
omit [ToString _] in
theorem t10 (a : α) (b : β) : True :=
  let _ := toString a; let _ := toString b; trivial
end

/-! illegal `omit`s -/

/-- error: invalid 'omit', 'α' has not been declared in the current scope -/
#guard_msgs in
variable (a : α) in
omit α in
theorem t11 (a : α) : True := trivial

/--
error: cannot omit referenced section variable 'α'
---
error: cannot omit referenced section variable 'α'
-/
#guard_msgs in
variable (α : Type) in
omit α in
theorem t12 (a : α) : True := trivial

/--
error: cannot omit referenced section variable 'inst✝'
---
error: cannot omit referenced section variable 'inst✝'
-/
#guard_msgs in
variable [ToString α] in
omit [ToString α] in
theorem t13 (a : α) : toString a = toString a := rfl

/--
error: application type mismatch
  ToString True
argument
  True
has type
  Prop : Type
but is expected to have type
  Type ?u.1758 : Type (?u.1758 + 1)
-/
#guard_msgs in
omit [ToString True]

/-- error: '[ToString Nat]' did not match any variables in the current scope -/
#guard_msgs in
omit [ToString Nat]

/-! `omit` can also be used to revert an `include` -/

variable (α : Type) in
include α in
omit α in
theorem t13 : True := trivial

/-- warning: included section variable 'α' is not used in 't14', consider excluding it -/
#guard_msgs in
variable (α : Type) in
include α in
omit α in
include α in
theorem t14 : True := trivial

/-! But you probably shouldn't use it -/

set_option linter.omit true in
/--
warning: `omit` should be avoided in favor of restructuring your `variable` declarations
note: this linter can be disabled with `set_option linter.omit false`
-/
#guard_msgs in
variable (α : Type) in
include α in
omit α in
theorem t15 : True := trivial
