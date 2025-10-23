import Std.Tactic.Do

open Std.Do

set_option warn.sorry false
set_option mvcgen.warning false

def foo (l : List Nat) : Nat := Id.run do
  let mut out := 0
  for _ in l do
    out := out + 1
  return out

def bar (n : Nat) : Nat := Id.run do
  let mut out := 0
  for _ in 0...n do
    out := out + 1
  return out

/-- This works as expected: -/
theorem foo_eq (l : List Nat) : foo l = l.length := by
  generalize h : foo l = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, out⟩ => ⌜True⌝
  case vc1 => sorry
  case vc2 => sorry
  case vc3 => sorry

/-- This used to fail in `inv1` due to an unresolved `HasFiniteRanges` instance: -/
theorem bar_eq (n : Nat) : bar n = n := by
  generalize h : bar n = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    -- Invalid match expression: The type of pattern variable 'xs' contains metavariables:
    -- (0...n).toList.Cursor
    exact ⇓⟨xs, out⟩ => ⌜True⌝
  case vc1 => sorry
  case vc2 => sorry
  case vc3 => sorry

theorem bar_eq' (n : Nat) : bar n = n := by
  generalize h : bar n = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, out⟩ => ⌜True⌝
  case vc1 => sorry
  case vc2 => sorry
  case vc3 => sorry

/-- Check the same for `mspec` -/
theorem bar_eq_mspec (n : Nat) : bar n = n := by
  generalize h : bar n = x
  apply Id.of_wp_run_eq h
  mspec
  -- should not produce a goal for `Std.PRange.HasFiniteRanges Std.PRange.BoundShape.open Nat`
  fail_if_success case inst => exact inferInstance
  all_goals sorry
