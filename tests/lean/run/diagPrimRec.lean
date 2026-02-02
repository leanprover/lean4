def fact1 : Nat → Nat := @Nat.rec
  (motive := fun _ => Nat)
  1
  (fun k ih => (k.add 1).mul ih)

/--
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 101, num: 1):
    [kernel] fact1 ↦ 101
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 50 in
example : fact1 100 = fact1 100 := by decide +kernel

def fact2 (t : Nat) : Nat := Nat.rec
  (motive := fun _ => Nat)
  1
  (fun k ih => (k.add 1).mul ih) t

/--
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 101, num: 1):
    [kernel] fact2 ↦ 101
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 50 in
example : fact2 100 = fact2 100 := by decide +kernel

def fact3 (n k : Nat) : Nat := @Nat.rec
  (motive := fun _ => Nat)
  k
  (fun k ih => (k.add 1).mul ih)
  n

/--
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 101, num: 1):
    [kernel] Nat.rec ↦ 101
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 50 in
example : fact3 100 1 = fact3 100 1 := by decide +kernel
