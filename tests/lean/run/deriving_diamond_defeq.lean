/-!
# Delta Deriving Diamond Fix Test

This test demonstrates a fix for a diamond problem in delta deriving.

## The Problem

When deriving an instance for a type alias like `def MyAlias := Underlying`, the
delta deriving handler:
1. Unfolds the alias to find the underlying type
2. Synthesizes instances for the underlying type
3. Creates a derived instance for the alias

The bug: instance-implicit class parameters in the derived instance TYPE were
using instances synthesized for the UNDERLYING type, not the ALIAS type.

This causes a diamond when:
- The alias has its own instance for a dependency class (e.g., from a CommSemiring)
- The underlying type also has an instance (e.g., WithTop.addMonoidWithOne)
- These are defeq but different expressions
- Instance search uses the alias's instance, but the derived instance uses the underlying's

## The Fix

After synthesis succeeds, for each instance-implicit class parameter:
1. Re-synthesize the instance for the TARGET type (the alias)
2. If it's defeq to what we synthesized for the underlying type, use the target's
3. This ensures the derived instance type matches what instance search expects

## This Test

We create two different instance EXPRESSIONS for `MyBase` that are DEFINITIONALLY EQUAL:
- `instBaseNat` for `Nat` with `value := 42`
- `instBaseMyAlias` for `MyAlias` with `value := 42` (same, so defeq)

Before the fix: `deriving instance MyHigher for MyAlias` would create:
  `instMyHigherMyAlias : @MyHigher MyAlias instBaseNat`
  Instance search for `MyHigher MyAlias` finds `instBaseMyAlias`, no match → fails

After the fix: `deriving instance MyHigher for MyAlias` creates:
  `instMyHigherMyAlias : @MyHigher MyAlias instBaseMyAlias`
  Instance search finds `instBaseMyAlias`, matches → succeeds
-/

-- A base class with a simple value
class MyBase (α : Type) where
  value : Nat := 42  -- default value

-- A higher class that requires MyBase
class MyHigher (α : Type) [MyBase α] : Prop where
  prop : True

-- Instance for Nat using default
instance instBaseNat : MyBase Nat := {}  -- value = 42

-- A NON-reducible type alias (like `def ENat := WithTop ℕ`)
def MyAlias := Nat

-- Instance for MyAlias ALSO using default
-- This is a DIFFERENT expression than instBaseNat, but DEFEQ since both have value=42
-- (Like AddMonoidWithOne from CommSemiring vs WithTop.addMonoidWithOne)
instance instBaseMyAlias : MyBase MyAlias := {}  -- value = 42

-- Verify they're defeq (would fail if values differed)
example : @MyBase.value Nat instBaseNat = @MyBase.value MyAlias instBaseMyAlias := rfl

-- Instance of MyHigher for Nat
instance instHigherNat : MyHigher Nat where
  prop := trivial

-- Derive MyHigher for MyAlias
deriving instance MyHigher for MyAlias

-- Check the instance type - must use instBaseMyAlias (the target type's instance), not instBaseNat.
-- This would have failed prior to https://github.com/leanprover/lean4/pull/12339
/--
info: instMyHigherMyAlias : @MyHigher MyAlias instBaseMyAlias
-/
#guard_msgs in
set_option pp.all true in
#check @instMyHigherMyAlias

/--
info: @[instance_reducible] def instMyHigherMyAlias : @MyHigher MyAlias instBaseMyAlias :=
instHigherNat
-/
#guard_msgs in
set_option pp.all true in
#print instMyHigherMyAlias

-- Instance search must succeed!
-- This worked on `master`, but would be broken by https://github.com/leanprover/lean4/pull/12179,
-- but is working again under 12179+12339.
-- This would fail before the fix because instance search uses instBaseMyAlias
-- but the derived instance had instBaseNat in its type
/--
info: inferInstance : MyHigher MyAlias
-/
#guard_msgs in
#check (inferInstance : MyHigher MyAlias)

-- Verify we can use the instance
example : (inferInstance : MyHigher MyAlias).prop = trivial := rfl
