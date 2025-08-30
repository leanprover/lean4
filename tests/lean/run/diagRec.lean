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
  [reduction] unfolded declarations (max: 64, num: 3):
    [reduction] Nat.rec ↦ 64
    [reduction] HAdd.hAdd ↦ 36
    [reduction] Acc.rec ↦ 33
  [reduction] unfolded reducible declarations (max: 64, num: 1):
    [reduction] Nat.casesOn ↦ 64
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 32 in
#reduce fib 10
