/-! This test ensures that local declarations explicitly passed to `grind` produce an appropriate
    error message, instead of just `unknown constant '...'`. -/

-- Checks that (invalid) identifiers which are not local declarations are still elaborated as global
-- constants.
/-- error: Unknown constant `h` -/
#guard_msgs in
example : 0 = 0 := by
  grind [h]

-- Checks the same property as before, but in the presence of the modifier `=`, which should not
-- affect how the subsequent identifier is resolved.
/-- error: Unknown constant `h` -/
#guard_msgs in
example : 0 = 0 := by
  grind [= h]

-- Checks that (valid) identifiers which are not local declarations are still elaborated as global
-- constants.
theorem t : 0 = 0 := rfl
example : 0 = 0 := by
  grind [= t]

-- Checks that local hypotheses do not shadow global constants.
def P := 0 = 0
example : 0 = 0 := by
  have P : 0 = 0 := rfl
  grind [P]

/-- error: redundant parameter `h`, `grind` uses local hypotheses automatically -/
#guard_msgs in
example : 0 = 0 := by
  have h : 1 = 1 := rfl
  grind [h]

/-- error: redundant parameter `h`, `grind` uses local hypotheses automatically -/
#guard_msgs in
example : 0 = 0 := by
  have h : 1 = 1 := rfl
  grind only [h]

-- Checks that dot notation on a local variable for a global theorem is accepted.
-- `n.triv` means `Nat.triv n`, not a local hypothesis.
theorem Nat.triv (n : Nat) : n = n := rfl

example (n : Nat) : n = n := by
  grind [n.triv]
