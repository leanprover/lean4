def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by a b => (a, b)

/--
info: [diag] Diagnostics
  [kernel] unfolded declarations (max: 1193, num: 5):
    [kernel] Nat.casesOn ↦ 1193
    [kernel] Nat.rec ↦ 1065
    [kernel] Eq.ndrec ↦ 973
    [kernel] Eq.rec ↦ 973
    [kernel] Acc.rec ↦ 754
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
info: [diag] Diagnostics
  [reduction] unfolded declarations (max: 2567, num: 5):
    [reduction] Nat.rec ↦ 2567
    [reduction] Eq.rec ↦ 1517
    [reduction] Acc.rec ↦ 1158
    [reduction] Or.rec ↦ 770
    [reduction] PSigma.rec ↦ 514
  [reduction] unfolded reducible declarations (max: 2337, num: 4):
    [reduction] Nat.casesOn ↦ 2337
    [reduction] Eq.ndrec ↦ 1307
    [reduction] Or.casesOn ↦ 770
    [reduction] PSigma.casesOn ↦ 514
  [kernel] unfolded declarations (max: 1193, num: 5):
    [kernel] Nat.casesOn ↦ 1193
    [kernel] Nat.rec ↦ 1065
    [kernel] Eq.ndrec ↦ 973
    [kernel] Eq.rec ↦ 973
    [kernel] Acc.rec ↦ 754
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
unseal ack in
set_option diagnostics.threshold 500 in
set_option diagnostics true in
theorem ex : ack 3 2 = 29 :=
  rfl
