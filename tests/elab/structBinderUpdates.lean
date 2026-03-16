/-!
# Tests of `structure` parameter binder updates

See also `inductiveBinderUpdates.lean`.
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
error: Only parameters appearing in the declaration header may have their binders kinds be overridden

Hint: If this is not intended to be an override, use a binder with a type: for example, `(x : _)`
-/
#guard_msgs in
class Inhabited where
  default (α) : α

end Ex4

/-!
Here, `(α β)` is not an override since `β` is not an existing parameter, so `α` is treated as a binder.
-/
namespace Ex5
/-- error: Failed to infer type of binder `α` -/
#guard_msgs in
class C (α : Type) where
  f (α β) : β
end Ex5

/-!
Here, `(α β)` is not an override since `β` is a field.
-/
namespace Ex6
/-- error: Failed to infer type of binder `α` -/
#guard_msgs in
class C (α : Type) where
  β : Type
  f (α β) : β
end Ex6

/-!
## Constructor updates
-/

/-!
Comparing natural constructor binder kinds to the updated ones.
-/
namespace ExC1

structure WithLp (p : Nat) (V : Type) where toLp ::
  ofLp : V

/-- info: constructor ExC1.WithLp.toLp : {p : Nat} → {V : Type} → V → WithLp p V -/
#guard_msgs in #print WithLp.toLp

structure WithLp' (p : Nat) (V : Type) where toLp (p) ::
  ofLp : V

/-- info: constructor ExC1.WithLp'.toLp : (p : Nat) → {V : Type} → V → WithLp' p V -/
#guard_msgs in #print WithLp'.toLp
end ExC1

/-!
Checking errors
-/
namespace ExC2

/-- error: Expecting binders that update binder kinds of type parameters. -/
#guard_msgs in
structure WithLp (p : Nat) (V : Type) where toLp (p : _) ::
  ofLp : V

variable (n : Nat)

/--
error: Only parameters appearing in the declaration header may have their binders kinds be overridden

Hint: If this is not intended to be an override, use a binder with a type: for example, `(x : _)`
-/
#guard_msgs in
structure WithLp (p : Nat) (V : Type) where toLp (n) ::
  ofLp : V

/-!
Even if `n` is used by `ofLp`, the restriction is still in place.
Motivation 1: the fields themselves have the same restriction, so it's for consistency.
Motivation 2: we should be able to tell whether the param binder update is legit without looking at all the fields.
Motivation 3: the constructor type is constructed before we know which `variable`s will be included. That would take participation of MutualInductive.
-/
/--
error: Only parameters appearing in the declaration header may have their binders kinds be overridden

Hint: If this is not intended to be an override, use a binder with a type: for example, `(x : _)`
-/
#guard_msgs in
structure WithLp (p : Nat) (V : Type) where toLp (n) ::
  ofLp : Fin n → V

/-- error: Expecting binders that update binder kinds of type parameters. -/
#guard_msgs in
structure WithLp (p : Nat) (V : Type) where toLp (m : Int) ::
  ofLp : V

end ExC2
