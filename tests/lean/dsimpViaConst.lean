/-! # `dsimp` uses theorems whose proofs are unapplied constants

This test ensures that `dsimp` can take advantage of `@[simp]` theorems whose proofs are unapplied
constants which are marked as `rfl` theorems.

## Context

To determine if a `@[simp]` theorem is a `rfl` theorem (and therefore usable by `dsimp`), we check
if its proof is one of the following:

1. directly a `rfl` proof, e.g. `Eq.rfl`
2. a `symm` proof of `rfl` proofs
3. an application of a constant which is considered a `rfl` theorem

This means that a theorem `foo` whose proofs is of the form `foo_internal_with_arg 0` where
`foo_internal_with_arg` is a `rfl` theorem. The first section
demonstrates that behavior as a control case.

We also want to consider a theorem a `rfl` theorem if its proof is simply:

4. a constant which is a `rfl` theorem

and is not necessarily applied to any arguments.

This behavior is ensured by the test case in the second section.

See issue #2685.
-/

/-- A wrapper which `dsimp` will eliminate after an appropriate `@[simp]` theorem is added. -/
def w : Bool → Bool | b => b

/-! # Control: `dsimp` uses applied constants -/

-- Check that `dsimp` makes no progress before we add the `@[simp]` theorem
example : w true = true := by dsimp

theorem foo_internal_with_arg (_ : Nat) : w true = true := rfl
@[simp] theorem foo_using_arg : w true = true := foo_internal_with_arg 0

example : w true = true := by dsimp


/-! # Test: `dsimp` uses unapplied constants -/

-- Check that `dsimp` makes no progress before we add the `@[simp]` theorem
example : w false = false := by dsimp

theorem foo_internal_without_arg : w false = false := rfl
@[simp] theorem foo_without_arg : w false = false := foo_internal_without_arg

example : w false = false := by dsimp
