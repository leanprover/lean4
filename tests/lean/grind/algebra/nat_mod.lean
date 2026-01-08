-- I'll start collecting particularly horrific examples
-- involving `Nat` modulo and div with variable denominators.

example (a b n : Nat) (ha : a < n) : (n - a) * b % n = (n - a * b % n) % n := by
  rw [Nat.sub_mul, Nat.mod_eq_mod_iff]
  match b with
  | 0 => refine ⟨1, 0, by simp⟩
  | b+1 =>
    refine ⟨a * (b + 1) / n, b, ?_⟩
    rw [Nat.mod_def, Nat.mul_add_one, Nat.mul_comm _ n, Nat.mul_comm b n]
    have : n * (a * (b + 1) / n) ≤ a * (b + 1) := Nat.mul_div_le (a * (b + 1)) n
    have := Nat.lt_mul_div_succ (a * (b + 1)) (show 0 < n by grind)
    have : a * (b + 1) ≤ n * b + n := by
      have := Nat.mul_le_mul_right b ha
      grind
    grind
