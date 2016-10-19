constants (A : Type.{1}) (f : A → A → A) (x y z : A) (g : A → A)
attribute [simp]
lemma foo : f x y = y := sorry
attribute [simp]
lemma bar : g y = z := sorry

open tactic

example : g (f x y) = z := by simp
example : g (f x (f x y)) = z := by simp
