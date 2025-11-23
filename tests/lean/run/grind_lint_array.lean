import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Array namespace: -/

#guard_msgs in
#grind_lint check (min := 20) in Array
