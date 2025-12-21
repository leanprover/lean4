import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Array namespace: -/

-- These go slightly over 20, but seem reasonable.
#grind_lint skip Array.count_singleton
#grind_lint skip Array.foldl_empty
#grind_lint skip Array.foldr_empty

#guard_msgs in
#grind_lint check (min := 20) in Array
