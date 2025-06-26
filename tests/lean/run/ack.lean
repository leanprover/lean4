def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by a b => (a, b)

/--
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 147, num: 3):
    [kernel] OfNat.ofNat ↦ 147
    [kernel] Add.add ↦ 61
    [kernel] HAdd.hAdd ↦ 61
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [simp] Diagnostics
  [simp] used theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57
  [simp] tried theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57, succeeded: 57
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 147, num: 3):
    [kernel] OfNat.ofNat ↦ 147
    [kernel] Add.add ↦ 61
    [kernel] HAdd.hAdd ↦ 61
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics.threshold 50 in
set_option diagnostics true in
theorem ex : ack 3 2 = 29 :=
  by simp [ack]
