import Lean

/-!
# Split of `[implicit_reducible]` and `[instance_reducible]`

After splitting `TransparencyMode.instances` into `.instances` and `.implicit`,
and `ReducibilityStatus.implicitReducible` into `.implicitReducible` and `.instanceReducible`:

  * `@[instance_reducible]` is auto-applied by the `instance` command and unfolds at
    `.instances` and above.
  * `@[implicit_reducible]` is user-applied and unfolds only at `.implicit`.

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

The declaration becomes implicit-reducible and no longer unfolds at `.instances`. -/

@[instance_reducible] def upgradeMe : Nat → Nat
  | n => n

attribute [implicit_reducible] upgradeMe

/-- info: @[implicit_reducible] def upgradeMe : Nat → Nat -/
#guard_msgs in
#print sig upgradeMe

open Lean Meta in
run_meta do
  let lhs := mkApp (mkConst ``upgradeMe) (mkNatLit 0)
  let rhs := mkNatLit 0
  let atInstances ← withTransparency .instances <| isDefEq lhs rhs
  match atInstances with
  | true => throwError "`upgradeMe` should not unfold at `.instances` after moving to `[implicit_reducible]`"
  | false => pure ()
  let atImplicit ← withTransparency .implicit <| isDefEq lhs rhs
  match atImplicit with
  | true => pure ()
  | false => throwError "`upgradeMe` should unfold at `.implicit`"

/-! ## A class-typed `def` is rejected if it lacks any reducibility attribute. -/

/--
warning: Definition `noAttr` of class type must be marked with `@[reducible]`, `@[instance_reducible]`, `@[implicit_reducible]` or `@[irreducible]`
-/
#guard_msgs in
def noAttr : Foo := ⟨42⟩

/-! ## Both `[instance_reducible]` and `[implicit_reducible]` accepted on class-typed `def`. -/

#guard_msgs in
@[instance_reducible] def withInstanceReducible : Foo := ⟨42⟩

#guard_msgs in
@[implicit_reducible] def withImplicitReducible : Foo := ⟨42⟩
