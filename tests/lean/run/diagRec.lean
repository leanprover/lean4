def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by n

/--
info: 89
---
info: unfolded declarations:
  Nat.rec ↦ 407
  Or.rec ↦ 144
  Acc.rec ↦ 108
unfolded reducible declarations:
  Nat.casesOn ↦ 352
  Or.casesOn ↦ 144
  PProd.fst ↦ 126
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
#reduce fib 10
