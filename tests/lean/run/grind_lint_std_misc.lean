import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check remaining Std sub-namespaces: -/

#guard_msgs in
#grind_lint check (min := 20) in Std.Do Std.Legacy.Range Std.Tactic
