/-!
Test that `grind` flags deprecated theorems.
See https://github.com/leanprover/lean4/issues/11582
-/
set_option backward.grind.inferPattern true  -- Use old pattern inference (no suggestions)
set_option linter.deprecated true  -- Enable the deprecated linter (test framework disables all linters)

def foo : Nat := 0

@[deprecated "use foo_eq_zero' instead" (since := "2025-01-01")]
theorem foo_eq_zero : foo = 0 := rfl

/-- warning: `foo_eq_zero` has been deprecated: use foo_eq_zero' instead -/
#guard_msgs in
example : foo = foo := by grind [foo_eq_zero]

-- Also test the `-` syntax for erasing theorems
@[grind]
theorem bar_eq_zero : foo = 0 := rfl

-- This theorem is deprecated AND marked with @[grind], so we can erase it
@[deprecated bar_eq_zero (since := "2025-01-01"), grind]
theorem bar_eq_zero' : foo = 0 := rfl

/-- warning: `bar_eq_zero'` has been deprecated: Use `bar_eq_zero` instead -/
#guard_msgs in
example : foo = foo := by grind [- bar_eq_zero']
