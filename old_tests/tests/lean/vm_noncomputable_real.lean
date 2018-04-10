def ℝ := set ℕ
constant ℝ.sub' : ℝ → ℝ → ℝ
noncomputable def ℝ.sub (a b : ℝ) := (λ b, a.sub' b) b
noncomputable instance : has_sub ℝ := ⟨ℝ.sub⟩
constant ℝ.nonneg : ℝ → Prop

-- This instance is computable, and the VM code generator should accept it.
instance : has_le ℝ := ⟨λ a b, (b - a).nonneg⟩