/-!
# Tests of `inductive` parameter binder updates

See also `structBinderUpdates.lean`.
-/

/-!
By default parameters are implicit.
-/
inductive Eq1 {α : Type u} (x : α) : α → Prop where
  | rfl : Eq1 x x
/-- info: Eq1.rfl.{u} {α : Type u} {x : α} : Eq1 x x -/
#guard_msgs in #check Eq1.rfl

/-!
Can override explicitness of the parameter for the constructor.
-/
inductive Eq2 {α : Type u} (x : α) : α → Prop where
  | rfl (x) : Eq2 x x
/-- info: Eq2.rfl.{u} {α : Type u} (x : α) : Eq2 x x -/
#guard_msgs in #check Eq2.rfl

/-!
Can override multiple parameter binders simultaneously.
-/
inductive Eq3 {α : Type u} (x : α) : α → Prop where
  | rfl (α x) : Eq3 x x
/-- info: Eq3.rfl.{u} (α : Type u) (x : α) : Eq3 x x -/
#guard_msgs in #check Eq3.rfl

/-!
There is no constraint on which parameter is overridden.
-/
inductive Eq4 {α : Type u} (x : α) : α → Prop where
  | rfl (α) : Eq4 x x
/-- info: Eq4.rfl.{u} (α : Type u) {x : α} : Eq4 x x -/
#guard_msgs in #check Eq4.rfl

/-!
Cannot override binders for parameters from from `variable`.
-/
/--
error: Only parameters appearing in the declaration header may have their binders kinds be overridden

Hint: If this is not intended to be an override, use a binder with a type: for example, `(x : _)`
-/
#guard_msgs in
variable {α : Type u} (x : α) in
inductive Eq5 : α → Prop where
  | rfl (x) : Eq5 x x

/-!
Test of the a header parameter shadowing a `variable` parameter that's still included as a parameter.
-/
variable {α : Type u} (x : α) in
inductive Eq6 (x : α) : α → Prop where
  | rfl (x) : Eq6 x (clear% x; x)
/-- info: Eq6.rfl.{u} {α : Type u} {x : α} (x✝ : α) : Eq6 x x✝ x -/
#guard_msgs in #check Eq6.rfl

/-!
The `(x)` syntax also can be used as a binder, if it's not shadowing a local variable.
-/
variable {α : Type u} in
inductive Eq7 : α → α → Prop where
  | rfl (x) : Eq7 x x
/-- info: Eq7.rfl.{u} {α : Type u} (x : α) : Eq7 x x -/
#guard_msgs in #check Eq7.rfl

/-!
Example of non-binder update.
-/
inductive I1 : Nat → Nat → Type where
  | mk (a b) : I1 a b
/-- info: I1.mk (a b : Nat) : I1 a b -/
#guard_msgs in #check I1.mk

/-!
Cannot mix binder updates with defining new fields.
When this happens, it assumes they're all new fields.
-/
/--
error: Mismatched inductive type parameter in
  I2 a b
The provided argument
  a
is not definitionally equal to the expected parameter
  a✝

Note: The value of parameter `a✝` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive I2 (a : Nat) : Nat → Type where
  | mk (a b) : I2 a b

/-!
Can mix binder updates with defining new fields if they're done in separate binders.
-/
inductive I2' (a : Nat) : Nat → Type where
  | mk (a) (b) : I2' a b
/-- info: I2'.mk (a b : Nat) : I2' a b -/
#guard_msgs in #check I2'.mk
