def fact : Nat → Nat := @Nat.rec
  (motive := fun _ => Nat)
  1
  (fun k ih => (k + 1) * ih)

/--
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 102, num: 6):
    [kernel] OfNat.ofNat ↦ 102
    [kernel] fact ↦ 101
    [kernel] Add.add ↦ 100
    [kernel] HAdd.hAdd ↦ 100
    [kernel] HMul.hMul ↦ 100
    [kernel] Mul.mul ↦ 100
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 50 in
theorem foo : fact 100 = fact 100 := by decide +kernel

def fact2 (n k : Nat) : Nat := @Nat.rec
  (motive := fun _ => Nat)
  k
  (fun k ih => (k + 1) * ih)
  n

/--
trace: [diag] Diagnostics
  [kernel] unfolded declarations (max: 102, num: 6):
    [kernel] OfNat.ofNat ↦ 102
    [kernel] Nat.rec ↦ 101
    [kernel] Add.add ↦ 100
    [kernel] HAdd.hAdd ↦ 100
    [kernel] HMul.hMul ↦ 100
    [kernel] Mul.mul ↦ 100
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 50 in
theorem bar : fact2 100 1 = fact2 100 1 := by decide +kernel
