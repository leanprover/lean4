def f (_ : Nat) := 10

set_option tactic.simp.trace true
example : f x = (if true then 8 + 2 else 0) := by
 simp
 rw [f]
