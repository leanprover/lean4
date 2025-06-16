/-!
# Tests of structure parameter binder updates
-/

/-!
Motivating issue: https://github.com/leanprover/lean4/issues/3574
Normally one defines a `cast_eq_zero_iff'` field and restates a `cast_eq_zero_iff` version.
-/
namespace Issue3574

class AddMonoidWithOne (R : Type u) extends Add R, Zero R where
  natCast : Nat → R

instance [AddMonoidWithOne R] : Coe Nat R where
  coe := AddMonoidWithOne.natCast
attribute [coe] AddMonoidWithOne.natCast

class CharP [AddMonoidWithOne R] (p : Nat) : Prop where
  cast_eq_zero_iff (R) (p) : ∀ x : Nat, (x : R) = 0 ↔ p ∣ x

-- Both `R` and `p` are explicit now.
/--
info: Issue3574.CharP.cast_eq_zero_iff.{u_1} (R : Type u_1) {inst✝ : AddMonoidWithOne R} (p : Nat) [self : CharP p]
  (x : Nat) : ↑x = 0 ↔ p ∣ x
-/
#guard_msgs in #check CharP.cast_eq_zero_iff

-- Multiple parameters can be updated at once.
class CharP' [AddMonoidWithOne R] (p : Nat) : Prop where
  cast_eq_zero_iff (R p) : ∀ x : Nat, (x : R) = 0 ↔ p ∣ x

/--
info: Issue3574.CharP'.cast_eq_zero_iff.{u_1} (R : Type u_1) {inst✝ : AddMonoidWithOne R} (p : Nat) [self : CharP' p]
  (x : Nat) : ↑x = 0 ↔ p ∣ x
-/
#guard_msgs in #check CharP'.cast_eq_zero_iff

end Issue3574

/-!
Basic test for structures.
-/
namespace Ex1

structure Inhabited (α : Type) where
  default : α

/-- info: Ex1.Inhabited.default {α : Type} (self : Inhabited α) : α -/
#guard_msgs in #check Inhabited.default

structure Inhabited' (α : Type) where
  default (α) : α

/-- info: Ex1.Inhabited'.default (α : Type) (self : Inhabited' α) : α -/
#guard_msgs in #check Inhabited'.default

end Ex1

/-!
Basic test for classes.
-/
namespace Ex2

class Inhabited (α : Type) where
  default : α

/-- info: Ex2.Inhabited.default {α : Type} [self : Inhabited α] : α -/
#guard_msgs in #check Inhabited.default

class Inhabited' (α : Type) where
  default (α) : α

/-- info: Ex2.Inhabited'.default (α : Type) [self : Inhabited' α] : α -/
#guard_msgs in #check Inhabited'.default

end Ex2

/-!
Example with a parameter from a `variable`
-/
namespace Ex3

class Inhabited (α : Type) where
  default : α

/-- info: Ex3.Inhabited.default {α : Type} [self : Inhabited α] : α -/
#guard_msgs in #check Inhabited.default

class Inhabited' (α : Type) where
  default (α) : α

/-- info: Ex3.Inhabited'.default (α : Type) [self : Inhabited' α] : α -/
#guard_msgs in #check Inhabited'.default

end Ex3

/-!
Trying to set a `variable` binder kind; only parameters in the declaration itself can be overridden.
Rationale: we found in mathlib that often users had large binder lists declared at the beginning of files,
and the structure fields accidentally were shadowing them.
-/
namespace Ex4

variable (α : Type)

/--
error: only parameters appearing in the declaration header may have their binders kinds be overridden

If this is not intended to be an override, use a binder with a type, for example '(x : _)'.
-/
#guard_msgs in
class Inhabited where
  default (α) : α

end Ex4

/-!
Here, `(α β)` is not an override since `β` is not an existing parameter, so `α` is treated as a binder.
-/
namespace Ex5
/-- error: failed to infer binder type -/
#guard_msgs in
class C (α : Type) where
  f (α β) : β
end Ex5

/-!
Here, `(α β)` is not an override since `β` is a field.
-/
namespace Ex6
/-- error: failed to infer binder type -/
#guard_msgs in
class C (α : Type) where
  β : Type
  f (α β) : β
end Ex6
