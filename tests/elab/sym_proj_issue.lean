import Lean

set_option linter.unusedVariables false in
def loopy : Option Nat := do
  let mut x  : Nat  := 0
  let mut y  : Nat  := 0
  let mut ok : Bool := false
  for _ in [:1] do
    x  := x + 1
    y  := y + 1
    ok := true
  return x

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : loopy = some 0 := by
  sym =>
    simp [loopy.eq_1]
    sorry
