constants (A : Type.{1}) (f : A → A → A) (x y z : A) (g : A → A)
lemma foo [simp] : f x y = y := sorry
lemma bar [simp] : g y = z := sorry

open tactic
set_option trace.simplifier true
example : g (f x y) = z := by simp >> triv
example : g (f x (f x y)) = z := by simp >> triv
