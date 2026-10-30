/-!
Regression test for #16026: `instantiate only` must fire instances delayed by
`grind_pattern ... where guard`, so `grind?` keeps the theorem in its suggestions.
-/

def f (n : Nat) : Nat := if n = 0 then 1 else 0

theorem f_eq_zero (n : Nat) (h : n ≠ 0) : f n = 0 := by simp [f, h]

grind_pattern f_eq_zero => f n where
  guard n ≠ 0

/--
info: Try these:
  [apply] grind only [usr f_eq_zero]
  [apply] grind => instantiate only [usr f_eq_zero]
-/
#guard_msgs in
example (n : Nat) (h : n ≠ 0) : f n = 0 := by grind?

example (n : Nat) (h : n ≠ 0) : f n = 0 := by grind only [usr f_eq_zero]

example (n : Nat) (h : n ≠ 0) : f n = 0 := by
  grind => instantiate only [usr f_eq_zero]
