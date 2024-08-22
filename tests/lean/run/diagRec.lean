def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by n

/--
info: 89
---
info: [reduction] unfolded declarations (max: 407, num: 3):
  [reduction] Nat.rec ↦ 407
  [reduction] Or.rec ↦ 144
  [reduction] Acc.rec ↦ 108[reduction] unfolded reducible declarations (max: 352, num: 2):
  [reduction] Nat.casesOn ↦ 352
  [reduction] Or.casesOn ↦ 144use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
#reduce fib 10
