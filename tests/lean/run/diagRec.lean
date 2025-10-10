@[semireducible]
def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by n

/--
info: 89
---
trace: [diag] Diagnostics
  [reduction] unfolded declarations (max: 497, num: 1):
    [reduction] Nat.rec ↦ 497
  [reduction] unfolded reducible declarations (max: 320, num: 1):
    [reduction] Nat.casesOn ↦ 320
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
#reduce fib 10
