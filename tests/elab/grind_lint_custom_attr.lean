import Lean.Elab.Tactic.Grind.Lint
import Lean.Meta.Tactic.Grind.RegisterCommand

register_grind_attr foo

@[foo =] theorem foo_add_zero (x : Nat) : x + 0 = x := by
  simp

#grind_lint skip foo_add_zero

/-- error: `foo_add_zero` is already in the `#grind_lint` skip set -/
#guard_msgs in
#grind_lint skip foo_add_zero
