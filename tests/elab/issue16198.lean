/-!
Regression test for #16198: `match` on `Float`/`Float32` literal patterns must compare literals by
value, not by how they are written. Distinct literals can denote the same float.
-/

-- As a `Float32`, `16777217` rounds to `16777216`.
example : (16777216 : Float32) = 16777217 := by decide

def f (s : Float32) (n : Nat) : Nat :=
  match s, n with
  | 16777216, 0 => 6
  | 16777217, _ => 7
  | _, _ => 0

/-- info: 7 -/
#guard_msgs in #eval f 16777217 1
/-- info: 6 -/
#guard_msgs in #eval f 16777217 0
/-- info: 0 -/
#guard_msgs in #eval f 1 1

example : f 16777217 1 = 7 := by decide
example : f 16777216 0 = 6 := by decide

def g (s : Float) (n : Nat) : Nat :=
  match s, n with
  | 5, 0 => 1
  | 5.0, _ => 2
  | 1.0, 0 => 3
  | 1, _ => 4
  | _, _ => 0

/-- info: [1, 2, 3, 4, 0] -/
#guard_msgs in #eval [g 5 0, g 5 1, g 1 0, g 1 1, g 2 0]

example : g 5 1 = 2 := by decide
example : g 1 1 = 4 := by decide
