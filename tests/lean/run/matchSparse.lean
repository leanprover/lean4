

import Lean
def expensive : Lean.Expr → Lean.Expr → Bool
  | .app (.app (.sort 1) (.sort 1)) (.sort 1), .app (.app (.sort 1) (.sort 1)) (.sort 1) => false
  | _, _ => true


/-- info: false -/
#guard_msgs in
#eval expensive (.app (.app (.sort 1) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1))

/-- info: true -/
#guard_msgs in
#eval expensive (.app (.app (.sort 2) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1))

example : expensive (.app (.app (.sort 1) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1)) = false := rfl
example : expensive (.app (.app (.sort 2) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1)) = true := rfl

#print expensive.match_1
#check expensive.match_1.eq_1
