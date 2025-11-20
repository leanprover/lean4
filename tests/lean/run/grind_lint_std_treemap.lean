import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Std tree map/set namespaces: -/

#guard_msgs in
#grind_lint check (min := 20) in Std.DTreeMap Std.TreeMap Std.TreeSet Std.ExtDTreeMap Std.ExtTreeMap Std.ExtTreeSet
