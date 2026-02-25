import Lean.LibrarySuggestions.Basic

/-!
# Tests for `maxSuggestions` parameter in `Simp.Config` and `Grind.Config`

This test verifies that the `maxSuggestions` field properly limits the number
of library suggestions passed to tactics when using `+suggestions`.
-/

section Grind

-- Define test theorems where only p3 helps with P 3
def P (_ : Nat) := True
theorem p1 : P 1 := trivial
theorem p2 : P 2 := trivial
theorem p3 : P 3 := trivial
theorem p4 : P 4 := trivial
theorem p5 : P 5 := trivial

-- Mock selector that returns suggestions respecting maxSuggestions
-- p3 is at position 3 (score 0.8)
set_library_suggestions (fun _ cfg => pure <|
  #[{ name := `p1, score := 1.0 },
    { name := `p2, score := 0.9 },
    { name := `p3, score := 0.8 },
    { name := `p4, score := 0.7 },
    { name := `p5, score := 0.6 }].take cfg.maxSuggestions)

-- Baseline: with default maxSuggestions, all 5 suggestions shown
/--
info: Library suggestions:
  p1 (score: 1.000000)
  p2 (score: 0.900000)
  p3 (score: 0.800000)
  p4 (score: 0.700000)
  p5 (score: 0.600000)
-/
#guard_msgs in
example : P 1 := by
  suggestions
  exact p1

-- KEY TEST: P 3 requires p3, which is at position 3
-- With maxSuggestions := some 2, grind only gets p1 and p2, so it FAILS
-- The diagnostics show p1 and p2 were received (not p3)
/--
error: `grind` failed
case grind
h : ¬P 3
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬P 3
    [prop] P 1
    [prop] P 2
  [eqc] True propositions
    [prop] P 1
    [prop] P 2
  [eqc] False propositions
    [prop] P 3
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] p1 ↦ 1
    [thm] p2 ↦ 1
-/
#guard_msgs in
example : P 3 := by grind +suggestions (maxSuggestions := some 2)

-- With maxSuggestions := some 3, grind gets p1, p2, p3, so it SUCCEEDS
#guard_msgs in
example : P 3 := by grind +suggestions (maxSuggestions := some 3)

end Grind

section Simp

-- Define simp lemmas where only s3 helps with the goal `c = true`
def a : Bool := true
def b : Bool := true
def c : Bool := true

theorem s1 : a = true := rfl
theorem s2 : b = true := rfl
theorem s3 : c = true := rfl
theorem s4 : a = a := rfl
theorem s5 : b = b := rfl

-- Mock selector for simp tests
set_library_suggestions (fun _ cfg => pure <|
  #[{ name := `s1, score := 1.0 },
    { name := `s2, score := 0.9 },
    { name := `s3, score := 0.8 },
    { name := `s4, score := 0.7 },
    { name := `s5, score := 0.6 }].take cfg.maxSuggestions)

-- With maxSuggestions := some 2, simp? only gets s1 and s2, so it can't prove c = true
/--
error: `simp` made no progress
-/
#guard_msgs in
example : c = true := by simp? +suggestions (maxSuggestions := some 2) only

-- With maxSuggestions := some 3, simp? gets s1, s2, s3, so it SUCCEEDS
/--
info: Try this:
  [apply] simp (maxSuggestions := some 3) only [s3]
-/
#guard_msgs in
example : c = true := by simp? +suggestions (maxSuggestions := some 3) only

end Simp
