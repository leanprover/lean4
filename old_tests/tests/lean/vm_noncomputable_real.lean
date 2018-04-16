def ℝ := set ℕ
constant ℝ.sub' : ℝ → ℝ → ℝ
/-
The following definition is accepted because the type is (ℝ → ℝ → ℝ) which is defeq to (ℝ → ℝ → ℕ → Prop).
The code generator can handle it because it is returning a type. Morally, it is the function that takes
three arguments and returns an unit.
-/
def ℝ.sub (a b : ℝ) := (λ b, a.sub' b) b
instance : has_sub ℝ := ⟨ℝ.sub⟩
constant ℝ.nonneg : ℝ → Prop
instance : has_le ℝ := ⟨λ a b, (b - a).nonneg⟩
