def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by a b => (a, b)

/--
info: [reduction] unfolded declarations (max: 1725, num: 4):
    Nat.rec ↦ 1725
  ⏎
  Eq.rec ↦ 1114
  ⏎
  Acc.rec ↦ 1050
  ⏎
  PSigma.rec ↦ 513[reduction] unfolded reducible declarations (max: 1577, num: 3):
    Nat.casesOn ↦ 1577
  ⏎
  Eq.ndrec ↦ 984
  ⏎
  PSigma.casesOn ↦ 513[kernel] unfolded declarations (max: 1193, num: 5):
    Nat.casesOn ↦ 1193
  ⏎
  Nat.rec ↦ 1065
  ⏎
  Eq.ndrec ↦ 973
  ⏎
  Eq.rec ↦ 973
   Acc.rec ↦ 754use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
unseal ack in
set_option diagnostics.threshold 500 in
set_option diagnostics true in
theorem ex : ack 3 2 = 29 :=
  rfl


/--
info: [kernel] unfolded declarations (max: 1193, num: 4):
    Nat.casesOn ↦ 1193
  ⏎
  Nat.rec ↦ 1065
  ⏎
  Eq.ndrec ↦ 973
   Eq.rec ↦ 973use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 800 in
theorem ack_3_2_eq_29 : ack 3 2 = 29 := by
  rfl -- uses kernel defeq checker, so only kernel diags shown
