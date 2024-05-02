def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by n

/--
info: 89
---
info: [reduction] unfolded declarations (max: 346, num: 3):
    Nat.rec ↦ 346
  ⏎
  Or.rec ↦ 116
  ⏎
  Acc.rec ↦ 104[reduction] unfolded reducible declarations (max: 296, num: 2):
    Nat.casesOn ↦ 296
  ⏎
  Or.casesOn ↦ 116use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
#reduce fib 10
