opaque q : Nat → Nat
def f (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x+1 => q (f x)

theorem f_eq : f (x + 1) = q (f x) := rfl
axiom q_eq (x : Nat) : q x = x

/--
info: [simp] used theorems (max: 50, num: 2):
    f_eq ↦ 50
  ⏎
  q_eq ↦ 50[simp] tried theorems (max: 261, num: 3):
    BitVec.of_length_zero ↦ 261
  ⏎
  f_eq ↦ 101
   q_eq ↦ 50use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : f (x + 50) = f x := by
  set_option diagnostics true in
  simp [f_eq, q_eq]

example : f (x + 50) = f x := by
  set_option diagnostics true in
  simp [f_eq, q_eq]

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

/--
info: [simp] used theorems (max: 1201, num: 3):
    ack.eq_3 ↦ 1201
  ⏎
  Nat.reduceAdd (builtin simproc) ↦ 771
  ⏎
  ack.eq_1 ↦ 768[simp] tried theorems (max: 3262, num: 3):
    BitVec.of_length_zero ↦ 3262
  ⏎
  ack.eq_3 ↦ 1973
   ack.eq_1 ↦ 768use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ack 4 4 = x := by
  set_option diagnostics true in
  simp [ack.eq_2, ack.eq_1, ack.eq_3]

/--
info: [simp] used theorems (max: 19, num: 5):
    ack.eq_3 ↦ 19
  ⏎
  Nat.reduceAdd (builtin simproc) ↦ 9
  ⏎
  ack.eq_1 ↦ 7
  ⏎
  ack.eq_2 ↦ 4
  ⏎
  Nat.zero_add ↦ 1[simp] tried theorems (max: 52, num: 5):
    BitVec.of_length_zero ↦ 52
  ⏎
  ack.eq_3 ↦ 30
  ⏎
  ack.eq_1 ↦ 7
  ⏎
  ack.eq_2 ↦ 4
   Nat.zero_add ↦ 1use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
error: tactic 'simp' failed, nested error:
(deterministic) timeout at `simp`, maximum number of heartbeats (500) has been reached
use `set_option maxHeartbeats <num>` to set the limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option maxHeartbeats 500 in
example : ack 4 4 = x := by
  set_option diagnostics true in
  set_option diagnostics.threshold 0 in
  simp [ack.eq_2, ack.eq_1, ack.eq_3]

@[reducible] def h (x : Nat) :=
  match x with
  | 0 => 10
  | x + 1 => h x

opaque q1 : Nat → Nat → Prop
@[simp] axiom q1_ax (x : Nat) : q1 x 10

/--
info: [simp] used theorems (max: 1, num: 1):
    q1_ax ↦ 1[simp] tried theorems (max: 7, num: 2):
    BitVec.of_length_zero ↦ 7
  ⏎
  q1_ax ↦ 1[reduction] unfolded declarations (max: 287, num: 2):
    Nat.rec ↦ 287
  ⏎
  OfNat.ofNat ↦ 28[reduction] unfolded instances (max: 14, num: 1):
    instOfNatNat ↦ 14[reduction] unfolded reducible declarations (max: 287, num: 2):
    h ↦ 287
   Nat.casesOn ↦ 287use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : q1 x (h 40) := by
  set_option diagnostics true in
  set_option diagnostics.threshold 0 in
  simp
