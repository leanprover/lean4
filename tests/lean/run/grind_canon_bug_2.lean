import Std.Data.ExtHashMap
open Std
set_option warn.sorry false

-- The following trace should contain only one `m[k]` and `(m.insert 1 3)[k]`
/--
trace: [grind.cutsat.model] k := 101
[grind.cutsat.model] (ExtHashMap.filter (fun k x => decide (101 ≤ k)) (m.insert 1 3))[k] := 4
[grind.cutsat.model] (m.insert 1 2)[k] := 4
[grind.cutsat.model] (m.insert 1 3)[k] := 4
[grind.cutsat.model] m[k] := 4
[grind.cutsat.model] (m.insert 1 2).getKey k ⋯ := 101
[grind.cutsat.model] m.getKey k ⋯ := 101
-/
#guard_msgs in
example (m : ExtHashMap Nat Nat) :
    (m.insert 1 2).filter (fun k _ => k > 1000) = (m.insert 1 3).filter fun k _ => k > 100 := by
  ext1 k
  set_option trace.grind.cutsat.model true in
  fail_if_success grind (splits := 4)
  sorry
