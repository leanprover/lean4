/-!
Tests the deprecated `splits` option of `grind`, which is ignored except that `splits := 0` disables
case-splits, and its deprecation warning. Its replacement `branches` is tested in
`elab/grind_branches.lean`.
-/

/--
warning: `splits` has been deprecated, use `branches` instead

Note: This linter can be disabled with `set_option linter.deprecated false`
-/
#guard_msgs in
set_option linter.deprecated true in
example (x : Int)
    (h : x ≤ 0 ∨ 100 ≤ x ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 14 ∨ x = 16 ∨ x = 18 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 26 ∨ x = 28 ∨ x = 30 ∨ x = 32 ∨ x = 34 ∨ x = 36)
    (h₁ : 0 < x) (h₂ : x < 100) (h₃ : x % 2 = 1) : False := by
  grind (splits := 3)

/--
warning: `splits` has been deprecated, use `branches` instead

Note: This linter can be disabled with `set_option linter.deprecated false`
---
error: `grind` has failed after reaching the threshold `(branches := 0)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option linter.deprecated true in
example (x : Int) (h : x = 1 ∨ x = 3) (h₁ : x % 2 = 0) : False := by
  grind (splits := 0)

/--
warning: `splits` has been deprecated, use `branches` instead

Note: This linter can be disabled with `set_option linter.deprecated false`
-/
#guard_msgs in
set_option linter.deprecated true in
example (x : Int) (h : x = 1 ∨ x = 3) (h₁ : x % 2 = 0) : False := by
  grind => finish (splits := 2)

-- No warning: the default value.
#guard_msgs in
set_option linter.deprecated true in
example (x : Int) (h : x = 1 ∨ x = 3) (h₁ : x % 2 = 0) : False := by
  grind (splits := 9)
