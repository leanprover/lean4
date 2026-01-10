import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Std tree map/set namespaces: -/

-- `Std.ExtTreeMap.getElem_filterMap'` is reasonable at 30.
#guard_msgs in
#grind_lint inspect (min := 35) Std.ExtTreeMap.getElem_filterMap'

-- `Std.TreeMap.getElem_filterMap'` is reasonable at 28.
#guard_msgs in
#grind_lint inspect (min := 30) Std.TreeMap.getElem_filterMap'

#guard_msgs in
#grind_lint check (min := 20) in Std.DTreeMap Std.TreeMap Std.TreeSet Std.ExtDTreeMap Std.ExtTreeMap Std.ExtTreeSet
