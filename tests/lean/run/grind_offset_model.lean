def g (i : Nat) (j : Nat) := i + j

set_option grind.debug true
set_option grind.debug.proofs true
set_option trace.grind.offset.model true

/--
trace: [grind.offset.model] i := 1
[grind.offset.model] j := 0
[grind.offset.model] 「0」 := 0
[grind.offset.model] 「i + 1」 := 2
-/
#guard_msgs (trace) in
example (i j : Nat) (h : i + 1 > j + 1) : g (i+1) j = i + 1 := by
  fail_if_success grind
  sorry

/--
trace: [grind.offset.model] i := 101
[grind.offset.model] 「0」 := 0
-/
#guard_msgs (trace) in
example (i : Nat) : i ≤ 100 := by
  fail_if_success grind
  sorry

/--
trace: [grind.offset.model] i := 99
[grind.offset.model] 「0」 := 0
-/
#guard_msgs (trace) in
example (i : Nat) : 100 ≤ i := by
  fail_if_success grind
  sorry

/--
trace: [grind.offset.model] n := 0
[grind.offset.model] j := 0
[grind.offset.model] i := 99
[grind.offset.model] 「0」 := 0
[grind.offset.model] 「n + 1」 := 1
-/
#guard_msgs (trace) in
example (i : Nat) : g (n + 1) m = a → 100 + j ≤ i := by
  fail_if_success grind
  sorry

/--
trace: [grind.offset.model] n := 0
[grind.offset.model] j := 101
[grind.offset.model] i := 0
[grind.offset.model] 「0」 := 0
[grind.offset.model] 「n + 1」 := 1
-/
#guard_msgs (trace) in
example (i : Nat) : g (n + 1) m = a → j ≤ i + 100 := by
  fail_if_success grind
  sorry
