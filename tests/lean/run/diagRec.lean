@[semireducible]
def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by n

/--
info: 377
---
info: [diag] Diagnostics
  [reduction] unfolded declarations (max: 653, num: 10):
    [reduction] Nat.rec ↦ 653
    [reduction] Or.rec ↦ 246
    [reduction] Acc.rec ↦ 147
    [reduction] Eq.rec ↦ 124
    [reduction] HAdd.hAdd ↦ 63
    [reduction] rfl ↦ 57
    [reduction] Nat.eq_or_lt_of_le ↦ 36
    [reduction] Add.add ↦ 34
    [reduction] sizeOf ↦ 25
    [reduction] Acc.inv ↦ 12
  [reduction] unfolded reducible declarations (max: 580, num: 5):
    [reduction] Nat.casesOn ↦ 580
    [reduction] Or.casesOn ↦ 246
    [reduction] Eq.ndrec ↦ 112
    [reduction] Nat.brecOn ↦ 36
    [reduction] Acc.recOn ↦ 12
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 10 in
#reduce fib 13
