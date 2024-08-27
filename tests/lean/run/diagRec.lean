def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
-- termination_by n

/--
info: 377
---
info: [reduction] unfolded declarations (max: 74, num: 3):
  [reduction] Nat.rec ↦ 74
  [reduction] HAdd.hAdd ↦ 22
  [reduction] Add.add ↦ 12[reduction] unfolded reducible declarations (max: 49, num: 1):
  [reduction] Nat.casesOn ↦ 49use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 10 in
#reduce fib 13
