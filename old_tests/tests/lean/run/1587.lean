def f (x : ℕ) := x

theorem foo : ∀ (x : ℕ), f x = x := by simp [f]

set_option pp.instantiate_mvars false

example (x : ℕ) : f x = x :=
begin
  transitivity, { refl, },
  rw [foo],
end

example (x : ℕ) : f x = x :=
begin
  transitivity, { refl, },
  simp [foo],
end

example : 8 + 4 ≤ 12 :=
begin
  transitivity,
  apply nat.add_le_add_right,
  { apply le_refl, },

  rw [norm_num.bit0_add_bit0],
end
