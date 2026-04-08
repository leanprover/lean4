import Lean

/-!
# Regression test: getEqnsFor? should not panic on matchers

Previously, when a theorem had a match expression in its type (e.g. `bar.match_1`),
calling `getEqnsFor?` on the matcher would panic with "duplicate normalized declaration name".

This was fixed by making `shouldGenerateEqnThms` return `false` for matchers, since
matcher equations are handled separately by `Lean.Meta.Match.MatchEqs`.
-/

-- A theorem with a match expression in its type creates a matcher `bar.match_1`
theorem bar : (match (0 : Nat) with | 0 => 0 | _ => 1) = 0 := by native_decide

-- getEqnsFor? on a matcher should return none (not panic)
/-- info: eqns: none -/
#guard_msgs in
#eval do
  let eqns ← Lean.Meta.getEqnsFor? `bar.match_1
  IO.println s!"eqns: {eqns}"

-- try? should not panic when encountering matchers in the goal
-- (it may fail to find suggestions, but should not panic)
/--
info: Try these:
  [apply] rfl
  [apply] simp
  [apply] simp only
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
theorem bar' : (match (0 : Nat) with | 0 => 0 | _ => 1) = 0 := by try?
