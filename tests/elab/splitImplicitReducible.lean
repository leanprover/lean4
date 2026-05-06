/-!
# Split of `[implicit_reducible]` and `[instance_reducible]`

After splitting `TransparencyMode.instances` into `.instances` (TC tier) and `.implicit`
(implicit-arg-defeq tier), and `ReducibilityStatus.implicitReducible` into
`.implicitReducible` and `.instanceReducible`:

  * `@[instance_reducible]` is auto-applied by the `instance` command and unfolds at
    `.instances` and above (used for type class diamond resolution).
  * `@[implicit_reducible]` is user-applied and unfolds only at `.implicit` and above
    (used for implicit-arg defeq, e.g. `Nat.add`, `Array.size`).

This file pins the new contract so we don't regress.
-/

/-! ## `instance` command stamps `instance_reducible`. -/

class Foo where
  x : Nat

instance instFoo : Foo := ⟨42⟩

/-- info: @[instance_reducible] def instFoo : Foo -/
#guard_msgs in
#print sig instFoo

/-! ## `@[implicit_reducible]` is preserved (no longer aliased to `instance_reducible`). -/

@[implicit_reducible] def myAdd : Nat → Nat → Nat
  | a, b => a + b

/-- info: @[implicit_reducible] def myAdd : Nat → Nat → Nat -/
#guard_msgs in
#print sig myAdd

/-! ## `[instance_reducible]` and `[implicit_reducible]` print distinctly. -/

@[instance_reducible] def myInstanceLike : Nat → Nat
  | n => n

/-- info: @[instance_reducible] def myInstanceLike : Nat → Nat -/
#guard_msgs in
#print sig myInstanceLike

/-! ## Upgrade transition: `[instance_reducible]` -> `[implicit_reducible]` is allowed.

This is the escape hatch for users who want an instance-tier symbol to *also* unfold
during implicit-arg defeq. -/

@[instance_reducible] def upgradeMe : Nat → Nat
  | n => n

attribute [implicit_reducible] upgradeMe

/-- info: @[implicit_reducible] def upgradeMe : Nat → Nat -/
#guard_msgs in
#print sig upgradeMe

/-! ## A class-typed `def` is rejected if it lacks any reducibility attribute. -/

/--
warning: Definition `noAttr` of class type must be marked with `@[reducible]` or `@[instance_reducible]`
-/
#guard_msgs in
def noAttr : Foo := ⟨42⟩

/-! ## Both `[instance_reducible]` and `[implicit_reducible]` accepted on class-typed `def`. -/

#guard_msgs in
@[instance_reducible] def withInstanceReducible : Foo := ⟨42⟩

#guard_msgs in
@[implicit_reducible] def withImplicitReducible : Foo := ⟨42⟩

/-! ## Sanity: instance-tier behavior continues to work. -/

example : (1 : Nat) + 2 = 3 := rfl
