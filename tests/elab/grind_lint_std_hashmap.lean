import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Std hash map/set namespaces: -/

-- `Std.ExtHashMap.getElem_filterMap'` is reasonable at 30.
#guard_msgs in
#grind_lint inspect (min := 35) Std.ExtHashMap.getElem_filterMap'

-- `Std.HashMap.getElem_filterMap'` is reasonable at 28.
#guard_msgs in
#grind_lint inspect (min := 30) Std.HashMap.getElem_filterMap'

#guard_msgs in
#grind_lint check (min := 20) in Std.DHashMap Std.HashMap Std.HashSet Std.ExtDHashMap Std.ExtHashMap Std.ExtHashSet
