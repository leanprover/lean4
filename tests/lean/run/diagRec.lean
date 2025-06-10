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
  [reduction] unfolded declarations (max: 540, num: 3):
    [reduction] Nat.rec ↦ 540
    [reduction] Or.rec ↦ 207
    [reduction] Acc.rec ↦ 108
  [reduction] unfolded reducible declarations (max: 478, num: 2):
    [reduction] Nat.casesOn ↦ 478
    [reduction] Or.casesOn ↦ 207
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
#reduce fib 10
