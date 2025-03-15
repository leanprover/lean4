def f (n : Nat) (m : Nat) :=
  if n < m then
    f (n+1) m + n
  else
    n

/--
info: [grind.ematch.instance] f.eq_def: f 5 m = if 5 < m then f (5 + 1) m + 5 else 5
-/
#guard_msgs (info) in
set_option trace.grind.ematch.instance true in
example : f 5 m > 0 := by
  fail_if_success grind (splits := 0) [f.eq_def]
  sorry

/-- info: [grind.ematch.instance] f.eq_def: f 5 m = if 5 < m then f (5 + 1) m + 5 else 5 -/
#guard_msgs (info) in
set_option trace.grind.ematch.instance true in
example : f 5 m > 0 := by
  grind (splits := 1) [f.eq_def]
