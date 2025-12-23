import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Array namespace: -/

-- These go slightly over 20, but seem reasonable.
#guard_msgs in
#grind_lint inspect (min := 22) Array.count_singleton
#guard_msgs in
#grind_lint inspect (min := 22) Array.foldl_empty
#guard_msgs in
#grind_lint inspect (min := 22) Array.foldr_empty

#guard_msgs in
#grind_lint check (min := 20) in Array
