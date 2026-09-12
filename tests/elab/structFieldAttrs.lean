-- Tests for attributes on structure fields.
-- Attributes on fields are applied to the generated projection functions.

import Lean

/-! ### @[deprecated] on a field -/

structure Foo where
  @[deprecated "Use y instead!" (since := "2025-04-30")] x : Nat
  y : Bool

/-! ### @[inline] on a field -/

structure Baz where
  @[inline] compute : Nat → Nat

/-! ### @[reducible] on a class field (class projections are semireducible by default) -/

class MyClass (α : Type) where
  @[reducible] default : α

/-! ### Field with default -/

structure WithDefault where
  @[deprecated "Stop!" (since := "2025-04-30")] x : Nat := 42

/-! ### Verify attributes were applied to projections -/

/-- info: true -/
#guard_msgs in
#eval do return Lean.Linter.isDeprecated (← Lean.getEnv) ``Foo.x

/-- info: true -/
#guard_msgs in
#eval do return Lean.Linter.isDeprecated (← Lean.getEnv) ``WithDefault.x
