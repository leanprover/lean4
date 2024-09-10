def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by a b => (a, b)

/--
info: [reduction] unfolded declarations (max: 1725, num: 4):
  [reduction] Nat.rec ↦ 1725
  [reduction] Eq.rec ↦ 1114
  [reduction] Acc.rec ↦ 1050
  [reduction] PSigma.rec ↦ 513[reduction] unfolded reducible declarations (max: 1577, num: 3):
  [reduction] Nat.casesOn ↦ 1577
  [reduction] Eq.ndrec ↦ 984
  [reduction] PSigma.casesOn ↦ 513[kernel] unfolded declarations (max: 1193, num: 5):
  [kernel] Nat.casesOn ↦ 1193
  [kernel] Nat.rec ↦ 1065
  [kernel] Eq.ndrec ↦ 973
  [kernel] Eq.rec ↦ 973
  [kernel] Acc.rec ↦ 754use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
unseal ack in
set_option diagnostics.threshold 500 in
set_option diagnostics true in
theorem ex : ack 3 2 = 29 :=
  rfl
