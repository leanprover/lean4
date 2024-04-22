import Lean
open Lean

#eval [1,2,3,]
#eval (2,3,)
#eval [1,2,3,,] -- Errors, double trailing comma
#eval (4,5,,,) -- ditto

axiom zeroAdd (x : Nat) : 0 + x = x
theorem rewrite_comma (x y z: Nat) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
  rewrite [zeroAdd,] at *;
  subst x;
  subst y;
  exact rfl

theorem simp_comma (x: Nat) : x = x := by
  simp [zeroAdd,]
