import Lean
/-!
Tests that `isDefEq` decides constraints between `Float`/`Float32` literals by value. Lazy delta
reduction used to unfold the float model on both sides, which timed out, e.g. when generating
equation lemmas for a `match` on float literals.
-/

open Lean Meta Elab Term

set_option maxHeartbeats 20000

def checkDefEq (x y : TermElabM Syntax) : TermElabM Unit := do
  let a ← elabTermAndSynthesize (← x) none
  let b ← elabTermAndSynthesize (← y) none
  logInfo m!"{a} =?= {b}: {← isDefEq a b}"

/-- info: 5 =?= 1.0: false -/
#guard_msgs in #eval checkDefEq `((5 : Float)) `((1.0 : Float))
/-- info: 0.1 =?= 0.10: true -/
#guard_msgs in #eval checkDefEq `((0.1 : Float)) `((0.10 : Float))
/-- info: -0.5 =?= -0.50: true -/
#guard_msgs in #eval checkDefEq `((-0.5 : Float)) `((-0.50 : Float))
/-- info: 0.0 =?= -0.0: false -/
#guard_msgs in #eval checkDefEq `((0.0 : Float)) `((-0.0 : Float))
/-- info: 1e30 =?= 20e29: false -/
#guard_msgs in #eval checkDefEq `((1e30 : Float)) `((2.0e30 : Float))
/-- info: 16777216 =?= 16777217: true -/
#guard_msgs in #eval checkDefEq `((16777216 : Float32)) `((16777217 : Float32))
/-- info: 1.5 =?= 2.5: false -/
#guard_msgs in #eval checkDefEq `((1.5 : Float32)) `((2.5 : Float32))

-- Equal values are accepted by the kernel too.
example : (0.1 : Float) = 0.10 := rfl
example : (16777216 : Float32) = 16777217 := rfl

-- At reducible transparency, distinct literals denoting the same value are not identified.
/-- info: 0.1 =?= 0.10: false -/
#guard_msgs in #eval withReducible <| checkDefEq `((0.1 : Float)) `((0.10 : Float))

-- `contradiction` does not get stuck on a hypothesis comparing distinct literals.
example (n : Nat) (x : (5 : Float) = 1.0 → False) (h : n ≠ n) : False := by
  contradiction

-- Equation lemmas for a `match` on float literals.
def h (s : Float) (n : Nat) : Nat :=
  match s, n with
  | 5, 0 => 1
  | 1.0, _ => 2
  | _, _ => 0

/-- info: h.eq_2 (n : Nat) : h 1.0 n = 2 -/
#guard_msgs in #check h.eq_2
/--
info: h.eq_3 (s : Float) (n : Nat) (x_3 : s = 1.0 → False) (x_2 : s = 5 → n = 0 → False) : h s n = 0
-/
#guard_msgs in #check h.eq_3

example (n : Nat) : h 1.0 n = 2 := by simp [h]

-- Equation lemmas for a `match` with overlapping literals denoting the same value (#16198).
def g (s : Float) (n : Nat) : Nat :=
  match s, n with
  | 5, 0 => 1
  | 5.0, _ => 2
  | 1.0, 0 => 3
  | 1, _ => 4
  | _, _ => 0

/-- info: g.eq_2 (n : Nat) (x_1 : n = 0 → False) : g 5.0 n = 2 -/
#guard_msgs in #check g.eq_2

example (n : Nat) (hn : n ≠ 0) : g 5.0 n = 2 := g.eq_2 n hn
