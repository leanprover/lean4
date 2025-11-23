def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by structural n

/--
info: 573147844013817084101
---
trace: [diag] Diagnostics
  [reduction] unfolded declarations (max: 596, num: 2):
    [reduction] Nat.rec ↦ 596
    [reduction] HAdd.hAdd ↦ 196
  [reduction] unfolded reducible declarations (max: 397, num: 1):
    [reduction] Nat.casesOn ↦ 397
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
#reduce fib 100
