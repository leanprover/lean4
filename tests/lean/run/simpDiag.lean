opaque q : Nat → Nat
def f (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x+1 => q (f x)

theorem f_eq : f (x + 1) = q (f x) := rfl
axiom q_eq (x : Nat) : q x = x

/--
info: [simp] Diagnostics
  [simp] used theorems (max: 50, num: 2):
    [simp] f_eq ↦ 50
    [simp] q_eq ↦ 50
  [simp] tried theorems (max: 101, num: 2):
    [simp] f_eq ↦ 101, succeeded: 50
    [simp] q_eq ↦ 50, succeeded: 50
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
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
info: [simp] Diagnostics
  [simp] used theorems (max: 1201, num: 3):
    [simp] ack.eq_3 ↦ 1201
    [simp] Nat.reduceAdd (builtin simproc) ↦ 771
    [simp] ack.eq_1 ↦ 768
  [simp] tried theorems (max: 1973, num: 2):
    [simp] ack.eq_3 ↦ 1973, succeeded: 1201
    [simp] ack.eq_1 ↦ 768, succeeded: 768
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
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

-- TODO: In the following test we just want to check whether we
-- diagnostics for `simp` when there is a failure. However, the
-- actual counters make the test very unstable since small
-- changes to Lean affect heartbeat consumption, and consequently
-- the number of rewrites tried.
-- /--
-- info: [simp] used theorems (max: 22, num: 5):
--     ack.eq_3 ↦ 22
--   ⏎
--   Nat.reduceAdd (builtin simproc) ↦ 14
--   ⏎
--   ack.eq_1 ↦ 11
--   ⏎
--   ack.eq_2 ↦ 4
--   ⏎
--   Nat.zero_add ↦ 1[simp] tried theorems (max: 38, num: 4):
--     ack.eq_3 ↦ 38, succeeded: 22
--   ⏎
--   ack.eq_1 ↦ 11, succeeded: 11
--   ⏎
--   ack.eq_2 ↦ 4, succeeded: 4
--   ⏎
--   Nat.zero_add ↦ 1, succeeded: 1[reduction] unfolded reducible declarations (max: 7, num: 1):
--     outParam ↦ 7use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-- ---
-- error: tactic 'simp' failed, nested error:
-- (deterministic) timeout at `whnf`, maximum number of heartbeats (500) has been reached
-- use `set_option maxHeartbeats <num>` to set the limit
-- use `set_option diagnostics true` to get diagnostic information
-- -/
-- #guard_msgs in
-- set_option maxHeartbeats 500 in
-- example : ack 4 4 = x := by
--   set_option diagnostics true in
--   set_option diagnostics.threshold 0 in
--   simp [ack.eq_2, ack.eq_1, ack.eq_3]

@[reducible] def h (x : Nat) :=
  match x with
  | 0 => 10
  | x + 1 => h x

opaque q1 : Nat → Nat → Prop
@[simp] axiom q1_ax (x : Nat) : q1 x 10

/--
info: [simp] Diagnostics
  [simp] used theorems (max: 1, num: 1):
    [simp] q1_ax ↦ 1
  [simp] tried theorems (max: 1, num: 1):
    [simp] q1_ax ↦ 1, succeeded: 1
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
info: [diag] Diagnostics
  [reduction] unfolded declarations (max: 246, num: 2):
    [reduction] Nat.rec ↦ 246
    [reduction] OfNat.ofNat ↦ 24
  [reduction] unfolded reducible declarations (max: 246, num: 2):
    [reduction] h ↦ 246
    [reduction] Nat.casesOn ↦ 246
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : q1 x (h 40) := by
  set_option diagnostics true in
  set_option diagnostics.threshold 0 in
  simp

example : q1 x (h 40) := by
  set_option diagnostics true in
  set_option diagnostics.threshold 0 in
  simp
