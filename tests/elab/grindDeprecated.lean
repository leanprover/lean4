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
/--
warning: `bar_eq_zero'` is deprecated, but the `[grind]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[deprecated bar_eq_zero (since := "2025-01-01"),̵ ̵g̵r̵i̵n̵d̵]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[deprecated bar_eq_zero (since := "2025-01-01"), grind]
theorem bar_eq_zero' : foo = 0 := rfl

-- Erasing it is not reported, since it can only be erased by its own name
#guard_msgs in
example : foo = foo := by grind [- bar_eq_zero']
