/-! This file tests kernel diagnostics reporting, triggered using the expensive `ack` function.  -/

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by a b => (a, b)

section async_true
/--
trace: [simp] Diagnostics
  [simp] used theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57
  [simp] tried theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57, succeeded: 57
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 176, num: 3):
    [kernel] OfNat.ofNat ↦ 176
    [kernel] Add.add ↦ 60
    [kernel] HAdd.hAdd ↦ 60
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics.threshold 50 in
set_option diagnostics true in
theorem ex : ack 3 2 = 29 :=
  by simp [ack]

end async_true

section async_false

set_option Elab.async false
/--
trace: [simp] Diagnostics
  [simp] used theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57
  [simp] tried theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57, succeeded: 57
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 174, num: 3):
    [kernel] OfNat.ofNat ↦ 174
    [kernel] Add.add ↦ 58
    [kernel] HAdd.hAdd ↦ 58
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics.threshold 50 in
set_option diagnostics true in
theorem ex2 : ack 3 2 = 29 :=
  by simp [ack]

end async_false

-- Check that kernel diagnostics are also reported in examples


/--
trace: [simp] Diagnostics
  [simp] used theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57
  [simp] tried theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57, succeeded: 57
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 174, num: 3):
    [kernel] OfNat.ofNat ↦ 174
    [kernel] Add.add ↦ 58
    [kernel] HAdd.hAdd ↦ 58
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics.threshold 50 in
set_option diagnostics true in
example : ack 3 2 = 29 :=
  by simp [ack]

-- Also in nested lemma

/--
trace: [simp] Diagnostics
  [simp] used theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57
  [simp] tried theorems (max: 57, num: 1):
    [simp] ack.eq_3 ↦ 57, succeeded: 57
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [diag] Diagnostics
  [def_eq] heuristic for solving `f a =?= f b` (max: 60, num: 1):
    [def_eq] ack ↦ 60
  [kernel] unfolded declarations (max: 174, num: 3):
    [kernel] OfNat.ofNat ↦ 174
    [kernel] Add.add ↦ 58
    [kernel] HAdd.hAdd ↦ 58
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics.threshold 50 in
set_option diagnostics true in
theorem ex3 : ack 3 2 = 29 :=
  by as_aux_lemma => simp [ack]
