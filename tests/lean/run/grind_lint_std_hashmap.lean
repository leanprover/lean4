import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Std hash/tree map/set namespaces: -/

#guard_msgs in
#grind_lint check (min := 20) in Std.DHashMap Std.HashMap Std.HashSet Std.ExtDHashMap Std.ExtHashMap Std.ExtHashSet
